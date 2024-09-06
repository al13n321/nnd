use crate::{*, symbols::*, arena::*, procfs::*, symbols_registry::*, util::*, context::*, executor::*};
use std::{mem, path::PathBuf, sync::{Arc, Mutex, atomic::{AtomicBool, AtomicUsize, Ordering}}, collections::HashSet, cmp, ops::Range, os::unix::ffi::OsStrExt, path::Path};
use std::arch::x86_64::*;
use rand::{random, distributions::Alphanumeric, thread_rng, Rng};

pub struct SymbolSearcher {
    pub searcher: Arc<dyn Searcher>,
    context: Arc<Context>,

    symbols: Vec<(BinaryId, Arc<Symbols>)>,
    pub waiting_for_symbols: bool, // if true, the `symbols` array is incomplete, but we may still be searching and have some results

    state: Arc<SearchState>,

    searched_query: SearchQuery,
    searched_num_symbols: usize,
}

const MAX_RESULTS: usize = 1000;

#[derive(Clone)]
pub struct SearchResults {
    pub results: Vec<SearchResult>, // limited to MAX_RESULTS
    pub total_results: usize, // not limited to MAX_RESULTS

    pub items_done: usize,
    pub items_total: usize, // not necessarily known in advance, may change during the search
    pub bytes_done: usize,

    pub complete: bool,
}
impl SearchResults {
    fn new() -> Self { Self {results: Vec::new(), total_results: 0, items_done: 0, items_total: 0, bytes_done: 0, complete: false} }
}

// Small and fast struct for a search match. We retrieve the slow full information (SearchResultInfo) only for the items on screen.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct SearchResult {
    score: usize,
    symbols_idx: usize, // index in SymbolSearcher's `symbols`
    id: usize,
}

#[derive(Clone)]
pub struct SearchResultInfo {
    pub id: usize,
    pub binary: BinaryId,
    pub symbols: Arc<Symbols>,

    pub name: String,
    pub mangled_name: String,
    pub file: PathBuf,
    pub line: LineInfo,

    pub name_match_ranges: Vec<Range<usize>>,
    pub file_match_ranges: Vec<Range<usize>>,
    pub mangled_name_match_ranges: Vec<Range<usize>>,
}
impl SearchResultInfo {
    fn new(binary: BinaryId, symbols: Arc<Symbols>, id: usize) -> Self { Self {binary, symbols, id, name: String::new(), mangled_name: String::new(), file: PathBuf::new(), line: LineInfo::invalid(), name_match_ranges: Vec::new(), file_match_ranges: Vec::new(), mangled_name_match_ranges: Vec::new()} }
}

// String with at least 32 bytes of readable memory before and after it, unless empty.
#[derive(Default, Eq, PartialEq, Debug, Clone)]
pub struct PaddedString {
    s: String,
}
impl PaddedString {
    pub fn new(a: &str) -> Self {
        let mut s = String::with_capacity(64 + a.len());
        s.push_str(unsafe {std::str::from_utf8_unchecked(&[0; 32])});
        s.push_str(a);
        s.push_str(unsafe {std::str::from_utf8_unchecked(&[0; 32])});
        Self {s}
    }

    pub fn get(&self) -> &str {
        if self.s.is_empty() {
            &self.s
        } else {
            &self.s[32..self.s.len()-32]
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone, Default)]
pub struct SearchQuery {
    pub s: PaddedString,
    pub case_sensitive: bool,
}
impl SearchQuery {
    pub fn parse(s: &str) -> Self {
        let case_sensitive = s.chars().any(|c| c.is_ascii_uppercase());
        Self {s: PaddedString::new(s), case_sensitive}
    }

    pub fn is_empty(&self) -> bool {
        self.s.get().is_empty()
    }
}

struct SearchState {
    results: Mutex<SearchResults>,
    cancel: AtomicBool,
    tasks_remaining: AtomicUsize,
}
impl SearchState {
    fn new() -> Self { Self {results: Mutex::new(SearchResults::new()), cancel: AtomicBool::new(false), tasks_remaining: AtomicUsize::new(0)} }
}

fn search_task(state: Arc<SearchState>, query: SearchQuery, symbols: Arc<Symbols>, symbols_idx: usize, shard_idx: usize, searcher: Arc<dyn Searcher>, context: Arc<Context>) {
    searcher.search(&symbols, symbols_idx, shard_idx, &query, &state.cancel, &mut |mut res: Vec<SearchResult>, delta_items_done: usize, delta_items_total: usize, delta_bytes_done: usize| -> bool {
        if state.cancel.load(Ordering::SeqCst) {
            return false;
        }

        let original_count = res.len();
        if res.len() > MAX_RESULTS {
            sort_and_truncate_results(&mut res);
        }

        let mut r = state.results.lock().unwrap();
        if !res.is_empty() {
            r.results.append(&mut res);
            sort_and_truncate_results(&mut r.results);
        }
        r.total_results += original_count;
        r.items_done = r.items_done.wrapping_add(delta_items_done);
        r.items_total = r.items_total.wrapping_add(delta_items_total);
        r.bytes_done = r.bytes_done.wrapping_add(delta_bytes_done);
        true
    });

    if !state.cancel.load(Ordering::SeqCst) && state.tasks_remaining.fetch_sub(1, Ordering::SeqCst) == 1 {
        {
            let mut r = state.results.lock().unwrap();
            r.complete = true;
        }

        context.wake_main_thread.write(1);
    }
}

fn sort_and_truncate_results(v: &mut Vec<SearchResult>) {
    v.sort_unstable_by_key(|r| r.score);
    v.truncate(MAX_RESULTS);
}

impl SymbolSearcher {
    pub fn new(searcher: Arc<dyn Searcher>, context: Arc<Context>) -> Self {
        let s = SymbolSearcher {searcher, context, symbols: Vec::new(), waiting_for_symbols: false, state: Arc::new(SearchState::new()), searched_query: SearchQuery::default(), searched_num_symbols: 0};
        s.state.results.lock().unwrap().complete = true;
        s
    }

    // Returns true if a new search started; the caller should scroll to top in this case.
    pub fn update(&mut self, registry: &SymbolsRegistry, query: &SearchQuery) -> bool {
        let seen_binary_ids: HashSet<BinaryId> = self.symbols.iter().map(|t| t.0.clone()).collect();
        self.waiting_for_symbols = false;
        let binaries = registry.list();
        for id in binaries {
            if seen_binary_ids.contains(&id) {
                continue;
            }
            let bin = registry.get_if_present(&id).unwrap();
            match &bin.symbols {
                Ok(s) => self.symbols.push((id.clone(), s.clone())),
                Err(e) if e.is_loading() => self.waiting_for_symbols = true,
                Err(_) => (),
            }
        }

        if (&self.searched_query, self.searched_num_symbols) == (query, self.symbols.len()) {
            return false;
        }

        self.state.cancel.store(true, Ordering::SeqCst);
        self.state = Arc::new(SearchState::new());

        self.searched_query = query.clone();
        self.searched_num_symbols = self.symbols.len();

        let mut tasks: Vec<(/*symbols_idx*/ usize, /*shard_idx*/ usize)> = Vec::new();
        let properties = self.searcher.properties();
        for idx in 0..self.symbols.len() {
            if properties.parallel {
                for shard_idx in 0..self.symbols[idx].1.shards.len() {
                    tasks.push((idx, shard_idx));
                }
            } else {
                tasks.push((idx, 0));
            }
        }
        self.state.tasks_remaining.store(tasks.len(), Ordering::SeqCst); // must happen before starting the tasks
        for (symbols_idx, shard_idx) in tasks {
            // TODO: Search by file+line if query starts with '@'; pre-filter file table and call a different method of Searcher.
            let (state, query, symbols, searcher, context) = (self.state.clone(), self.searched_query.clone(), self.symbols[symbols_idx].1.clone(), self.searcher.clone(), self.context.clone());
            self.context.executor.add(move || search_task(state, query, symbols, symbols_idx, shard_idx, searcher, context));
        }

        true
    }

    pub fn get_results(&self) -> SearchResults {
        (*self.state.results.lock().unwrap()).clone()
    }

    pub fn format_result(&self, r: &SearchResult) -> SearchResultInfo {
        let s = &self.symbols[r.symbols_idx];
        self.searcher.format_result(s.0.clone(), &s.1, &self.searched_query, r)
    }

    pub fn format_results(&self, results: &[SearchResult]) -> Vec<SearchResultInfo> {
        let mut res: Vec<SearchResultInfo> = Vec::new();
        for r in results {
            let s = &self.symbols[r.symbols_idx];
            res.push(self.searcher.format_result(s.0.clone(), &s.1, &self.searched_query, r));
        }
        res
    }
}
impl Drop for SymbolSearcher {
    fn drop(&mut self) {
        self.state.cancel.store(true, Ordering::SeqCst);
    }
}

// Called periodically during the search (e.g. every few MBs) to report new results, report progress, and check cancellation.
// Returns false if the search is cancelled.
pub type SearchCallback<'a> = dyn FnMut(Vec<SearchResult>, /*delta_items_done*/ usize, /*delta_items_total*/ usize, /*delta_bytes_done*/ usize) -> bool + 'a;

#[derive(Clone, Debug)]
pub struct SearcherProperties {
    pub have_names: bool,
    pub have_files: bool,
    pub have_mangled_names: bool,
    // If true, we schedule one task per SymbolsShard, otherwise one task per Symbols.
    pub parallel: bool,
}

pub trait Searcher: Sync + Send {
    fn search(&self, symbols: &Symbols, symbols_idx: usize, shard_idx: usize, query: &SearchQuery, cancel: &AtomicBool, callback: &mut SearchCallback);
    fn format_result(&self, binary: BinaryId, symbols: &Arc<Symbols>, query: &SearchQuery, res: &SearchResult) -> SearchResultInfo;
    fn properties(&self) -> SearcherProperties;
}

pub struct FileSearcher;

impl Searcher for FileSearcher {
    fn search(&self, symbols: &Symbols, symbols_idx: usize, shard_idx: usize, query: &SearchQuery, cancel: &AtomicBool, callback: &mut SearchCallback) {
        let items_total = symbols.path_to_used_file.len();
        callback(Vec::new(), 0, items_total, 0);
        let mut res: Vec<SearchResult> = Vec::new();
        let mut bytes_done = 0usize;
        let mut _match_ranges: Vec<Range<usize>> = Vec::new();
        for (path, &id) in &symbols.path_to_used_file {
            if cancel.load(Ordering::Relaxed) {
                return;
            }
            let slice = path.as_os_str().as_bytes();
            _match_ranges.clear();
            if let Some(score) = fuzzy_match(slice, query, &mut _match_ranges) {
                res.push(SearchResult {score, id, symbols_idx});
            }
            bytes_done += slice.len();
        }
        callback(res, items_total, 0, bytes_done);
    }

    fn format_result(&self, binary: BinaryId, symbols: &Arc<Symbols>, query: &SearchQuery, res: &SearchResult) -> SearchResultInfo {
        let file = &symbols.files[res.id];
        let mut res = SearchResultInfo::new(binary, symbols.clone(), res.id);
        res.file = file.path.to_owned();
        let slice = file.path.as_os_str().as_bytes();
        fuzzy_match(slice, query, &mut res.file_match_ranges);
        res
    }

    fn properties(&self) -> SearcherProperties { SearcherProperties {have_names: false, have_files: true, have_mangled_names: false, parallel: false} }
}

pub struct FunctionSearcher;

impl Searcher for FunctionSearcher {
    fn search(&self, symbols: &Symbols, symbols_idx: usize, shard_idx: usize, query: &SearchQuery, cancel: &AtomicBool, callback: &mut SearchCallback) {
        let query = modify_query_for_mangled_search(query);

        let range = (symbols.functions.len()*shard_idx/symbols.shards.len())..(symbols.functions.len()*(shard_idx+1)/symbols.shards.len());
        callback(Vec::new(), 0, range.len(), 0);
        let mut items_done = 0usize;
        let mut bytes_done = 0usize;
        let mut res: Vec<SearchResult> = Vec::new();
        let mut match_ranges: Vec<Range<usize>> = Vec::new();
        for idx in range {
            if idx & 127 == 0 && cancel.load(Ordering::Relaxed) {
                return;
            }
            let function = &symbols.functions[idx];
            if function.flags.contains(FunctionFlags::SENTINEL) {
                continue;
            }
            let slice = function.mangled_name();
            match_ranges.clear();
            if let Some(score) = fuzzy_match(slice, &query, &mut match_ranges) {
                res.push(SearchResult {score, id: idx, symbols_idx});
            }
            items_done += 1;
            bytes_done += slice.len();
            if items_done > (1 << 16) {
                if !callback(mem::take(&mut res), mem::take(&mut items_done), 0, mem::take(&mut bytes_done)) {
                    return;
                }
            }
        }
        callback(res, items_done, 0, bytes_done);
    }

    fn format_result(&self, binary: BinaryId, symbols: &Arc<Symbols>, query: &SearchQuery, res: &SearchResult) -> SearchResultInfo {
        let function = &symbols.functions[res.id];
        let mut res = SearchResultInfo::new(binary, symbols.clone(), res.id);
        res.name = function.demangle_name();
        res.mangled_name = String::from_utf8_lossy(function.mangled_name()).into_owned();
        if let Some((sf, _)) = symbols.root_subfunction(function) {
            if let Some(file_idx) = sf.call_line.file_idx() {
                res.file = symbols.files[file_idx].path.to_owned();
                res.line = sf.call_line.clone();
            }
        }
        let query = modify_query_for_mangled_search(query);
        fuzzy_match(res.mangled_name.as_bytes(), &query, &mut res.mangled_name_match_ranges);
        if fuzzy_match(res.name.as_bytes(), &query, &mut res.name_match_ranges).is_none() {
            res.name_match_ranges.clear();
        }
        res
    }

    fn properties(&self) -> SearcherProperties { SearcherProperties {have_names: true, have_files: true, have_mangled_names: true, parallel: true} }
}

fn modify_query_for_mangled_search(query: &SearchQuery) -> SearchQuery {
    let s: String = query.s.get().chars().filter(|&c| c.is_ascii_alphanumeric() || c == '_').collect();
    SearchQuery::parse(&s)
}

fn fuzzy_match(haystack: &[u8], query: &SearchQuery, match_ranges: &mut Vec<Range<usize>>) -> Option<usize> {
    // Scoring (smaller tuple - higher in results list):
    //  * 0 if the string is exactly equal to the query string.
    //  * (1, !is_suffix, alphanum_before, alphanum_after, haystack.len()) if the query string is a substring.
    //  * (2, k, haystack.len()) if the query string appears as a subsequence, with k contiguous pieces.
    //    Checking if it's a subsequence at all is trivial, but minimizing k takes O(n*m) time.
    //    We should do some approximation instead. Maybe find a subsequence greedily, then do one forward and one backward pass greedily coalescing the pieces.
    //  * MAX if not a match at all.

    let needle = query.s.get();
    assert_eq!(match_ranges.len(), 0);

    if needle.len() > haystack.len() {
        return None;
    }
    // Check the suffix separately (in case there are multiple occurrences; because we don't have backwards search).
    let (case, extra) = if memmem_maybe_case_sensitive(&haystack[haystack.len() - needle.len()..], &query.s, query.case_sensitive).is_some() {
        if haystack.len() == needle.len() {
            return Some(0);
        }
        match_ranges.push(haystack.len() - needle.len() .. haystack.len());
        let alphanum_before = haystack[haystack.len() - needle.len() - 1].is_ascii_alphanumeric();
        (1, 4usize | ((alphanum_before as usize) << 1))
    } else if let Some(i) = memmem_maybe_case_sensitive(&haystack[..haystack.len() - 1], &query.s, query.case_sensitive) {
        match_ranges.push(i..i+needle.len());
        let alphanum_before = i > 0 && haystack[i - 1].is_ascii_alphanumeric();
        let alphanum_after = i + needle.len() < haystack.len() && haystack[i + needle.len()].is_ascii_alphanumeric();
        (1, ((alphanum_before as usize) << 1) | alphanum_after as usize)
    } else {
        // Check if subsequence.
        let needle = needle.as_bytes();
        let mut match_start: Option<usize> = None;
        let (mut hay_i, mut needle_i) = (0usize, 0usize);
        while hay_i < haystack.len() && needle_i < needle.len() {
            let c = haystack[hay_i];
            let c = if query.case_sensitive {c} else {c.to_ascii_lowercase()};
            if c == needle[needle_i] {
                needle_i += 1;
                if match_start.is_none() {
                    match_start = Some(hay_i);
                }
            } else if let Some(s) = match_start {
                match_ranges.push(s..hay_i);
                match_start = None;
            }
            hay_i += 1;
        }
        if needle_i < needle.len() {
            return None;
        }
        if let Some(s) = match_start {
            match_ranges.push(s..hay_i);
        }
        // TODO: Do greedy coalescing of ranges.
        (2, match_ranges.len())
    };
    // Pack tuple into one number.
    Some((case << 61) | (extra << 32) | haystack.len())
}

#[cfg(target_feature = "avx2")]
pub fn memmem_maybe_case_sensitive(haystack: &[u8], needle: &PaddedString, case_sensitive: bool) -> Option<usize> {
    unsafe {
        let needle = needle.get();
        if needle.is_empty() {
            return Some(0);
        }
        if needle.len() > haystack.len() {
            return None;
        }

        let needle_len = needle.len();

        // Create constants for case conversion.
        let upper_a = _mm256_set1_epi8(b'A' as i8);
        let twenty_six = _mm256_set1_epi8(26);
        let lowercase_mask = _mm256_set1_epi8(if case_sensitive {0} else {32});

        unsafe fn compare(mut hay: __m256i, need: __m256i, upper_a: __m256i, twenty_six: __m256i, lowercase_mask: __m256i) -> u32 {
            let offset = _mm256_sub_epi8(hay, upper_a);
            let is_upper = _mm256_cmpgt_epi8(twenty_six, offset);
            hay = _mm256_or_si256(hay, _mm256_and_si256(is_upper, lowercase_mask));
            let cmp = _mm256_cmpeq_epi8(hay, need);
            _mm256_movemask_epi8(cmp) as u32
        }

        if needle_len > 32 {
            // Believe it or not, long needle is the more straightforward case.

            let first_32 = _mm256_loadu_si256(needle.as_ptr() as *const __m256i);
            let last_32 = _mm256_loadu_si256(needle[needle_len - 32..].as_ptr() as *const __m256i);

            for i in 0..=haystack.len() - needle_len {
                // First 32 bytes.
                let haystack_first = _mm256_loadu_si256(haystack[i..].as_ptr() as *const __m256i);
                if compare(haystack_first, first_32, upper_a, twenty_six, lowercase_mask) != u32::MAX {
                    continue;
                }

                // Last 32 bytes (potentially overlapping other 32-byte ranges we're checking).
                let haystack_last = _mm256_loadu_si256(haystack[i + needle_len - 32..].as_ptr() as *const __m256i);
                if compare(haystack_last, last_32, upper_a, twenty_six, lowercase_mask) != u32::MAX {
                    continue;
                }

                // Other blocks of 32 bytes.
                let mut j = 32;
                while j < needle_len - 32 {
                    let haystack_chunk = _mm256_loadu_si256(haystack[i + j..].as_ptr() as *const __m256i);
                    let needle_chunk = _mm256_loadu_si256(needle[j..].as_ptr() as *const __m256i);
                    if compare(haystack_chunk, needle_chunk, upper_a, twenty_six, lowercase_mask) != u32::MAX {
                        break;
                    }
                    j += 32;
                }
                if j >= needle_len - 32 {
                    return Some(i);
                }
            }
        } else {
            // This is tricky because AVX and SSE don't seem to have unaligned masked loads that don't segfault if the 32-byte range touches an unmapped page (even in the masked-off part).
            // We could require padding, but that seems overall more annoying than dealing with unpadded data in this function.
            // The padded version would be simple: for each i, we read haystack[i..i+32] into a register and check if the first needle_len bytes of the register match the needle.
            // But if i+32 > haystack.len(), and haystack is at the very end of the last mapped page, this read will segfault.
            // To avoid it, we introduce the second way of doing the comparison: read haystack[i+needle_len-32..i+needle_len] into a register and check if the *last* needle_len bytes match the needle.
            // The first way breaks near the end of a page, the second way breaks near the start of a page. So we switch between them as needed, such that we only ever touch aligned 32-byte blocks that touch the needle.

            // Load the needle into a SIMD register.
            let prefix_needle = _mm256_loadu_si256(needle.as_ptr() as *const __m256i);
            let prefix_mask = !0u32 >> (32 - needle_len);
            let suffix_needle = _mm256_loadu_si256(needle.as_ptr().add(needle_len).sub(32) as *const __m256i);
            let suffix_mask = !0u32 << (32 - needle_len);

            let switch_point = 32usize.wrapping_sub(haystack.as_ptr() as usize % 64);
            let switch_point = if switch_point > 32 { 0 } else { switch_point };

            // Using a prefix of the register.
            for i in 0..switch_point.min(haystack.len() - needle_len + 1) {
                let haystack_chunk = _mm256_loadu_si256(haystack[i..].as_ptr() as *const __m256i);
                if compare(haystack_chunk, prefix_needle, upper_a, twenty_six, lowercase_mask) & prefix_mask == prefix_mask {
                    return Some(i);
                }
            }

            // Using a suffix of the register.
            for i in switch_point..=haystack.len() - needle_len {
                let haystack_chunk = _mm256_loadu_si256(haystack.as_ptr().add(i + needle_len).sub(32) as *const __m256i);
                if compare(haystack_chunk, suffix_needle, upper_a, twenty_six, lowercase_mask) & suffix_mask == suffix_mask {
                    return Some(i);
                }
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use crate::search::*;

    #[test]
    fn test_memmem() {
        let mut rng = thread_rng();
        // Short enough that we'll hit empty substring case sometimes, long enough to have a few 32-byte blocks.
        let data: String = (0..300).map(|_| rng.sample(Alphanumeric) as char).collect();
        let mut temp = String::new();
        for i in 0..3000 {
            let hay_start = random::<usize>() % (data.len() + 1);
            let hay_len = random::<usize>() % (data.len() - hay_start + 1);
            let needle_start = random::<usize>() % (data.len() + 1);
            let needle_len = random::<usize>() % (data.len() - needle_start + 1).min(hay_len + 3);
            let case_sensitive = random::<bool>();
            let hay = &data[hay_start..hay_start + hay_len];
            let needle = &data[needle_start..needle_start + needle_len];

            temp.clear();
            temp.push_str(needle);
            if !case_sensitive {
                temp.make_ascii_lowercase();
            }
            let mut bad_needle = false;
            if i % 4 == 0 && needle_len != 0 {
                let c = rng.sample(Alphanumeric) as u8;
                bad_needle |= !case_sensitive && (c as char).is_ascii_uppercase();
                unsafe {temp.as_bytes_mut()[random::<usize>() % needle_len] = c};
            }
            let needle = &temp;

            let expected = if case_sensitive {
                hay.find(needle)
            } else if needle_len == 0 {
                Some(0)
            } else if bad_needle {
                None
            } else {
                hay.as_bytes().windows(needle_len).position(|w| unsafe {std::str::from_utf8_unchecked(w).eq_ignore_ascii_case(needle)})
            };

            let found = memmem_maybe_case_sensitive(hay.as_bytes(), &PaddedString::new(needle), case_sensitive);

            assert_eq!(expected, found, "{} {} {} {}", i, hay, needle, case_sensitive);
        }
    }
}
