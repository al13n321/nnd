use flate2::{write::ZlibEncoder, Compression};
use std::{
    env, fs,
    io::Write,
    path::{Path, PathBuf},
    process::Command,
};

const TABLE_NAMES: &[&str] = &[
    "ts_alias_sequences",
    "ts_non_terminal_alias_map",
    "ts_primary_state_ids",
    "ts_lex_modes",
    "ts_parse_table",
    "ts_small_parse_table",
    "ts_small_parse_table_map",
    "ts_parse_actions",
    "ts_external_scanner_symbol_map",
    "ts_external_scanner_states",
];

struct Grammar {
    package: &'static str,
    version: &'static str,
    name: &'static str,
    function: &'static str,
}

#[derive(Clone)]
struct TableDecl {
    name: String,
    c_type: String,
    start: usize,
    end: usize,
    size: usize,
}

struct PackedTable {
    grammar_idx: usize,
    table_idx: usize,
    static_name: String,
}

fn main() {
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let table_root = out_dir.join("tree_sitter_tables");
    let query_root = out_dir.join("tree_sitter_queries");
    fs::create_dir_all(&table_root).unwrap();
    fs::create_dir_all(&query_root).unwrap();

    let grammars = [
        Grammar {
            package: "tree-sitter-rust",
            version: "0.24.2",
            name: "rust",
            function: "tree_sitter_rust",
        },
        Grammar {
            package: "tree-sitter-c",
            version: "0.24.2",
            name: "c",
            function: "tree_sitter_c",
        },
        Grammar {
            package: "tree-sitter-cpp",
            version: "0.23.4",
            name: "cpp",
            function: "tree_sitter_cpp",
        },
        Grammar {
            package: "tree-sitter-zig",
            version: "1.1.2",
            name: "zig",
            function: "tree_sitter_zig",
        },
        Grammar {
            package: "tree-sitter-odin",
            version: "1.3.0",
            name: "odin",
            function: "tree_sitter_odin",
        },
    ];

    let mut cc_build = cc::Build::new();
    cc_build.std("c11").warnings(false);

    let mut packed_tables = Vec::new();
    let mut generated = String::new();
    generated.push_str(
        r#"use flate2::read::ZlibDecoder;
use std::{ffi::c_void, io::Read, sync::OnceLock};
use tree_sitter::Language;
use tree_sitter_language::LanguageFn;

struct TableData {
    words: Vec<u64>,
}

struct PackedTable {
    compressed: &'static [u8],
    size: usize,
    data: OnceLock<TableData>,
}

fn decode_table(table: &'static PackedTable, size: usize) -> *const c_void {
    if size != table.size {
        std::process::abort();
    }

    let data = table.data.get_or_init(|| {
        let mut words = vec![0u64; (table.size + 7) / 8];
        let out = unsafe {
            std::slice::from_raw_parts_mut(words.as_mut_ptr().cast::<u8>(), table.size)
        };
        let mut decoder = ZlibDecoder::new(table.compressed);
        if decoder.read_exact(out).is_err() {
            std::process::abort();
        }
        let mut trailing = [0u8; 1];
        match decoder.read(&mut trailing) {
            Ok(0) => {}
            _ => std::process::abort(),
        }
        TableData { words }
    });

    data.words.as_ptr().cast::<c_void>()
}

"#,
    );

    for (grammar_idx, grammar) in grammars.iter().enumerate() {
        let crate_dir = find_crate_source(grammar.package, grammar.version);
        let src_dir = crate_dir.join("src");
        let parser_path = src_dir.join("parser.c");
        let scanner_path = src_dir.join("scanner.c");
        println!("cargo:rerun-if-changed={}", parser_path.display());
        if scanner_path.exists() {
            println!("cargo:rerun-if-changed={}", scanner_path.display());
        }

        let parser = fs::read_to_string(&parser_path).unwrap();
        let mut table_decls: Vec<TableDecl> = TABLE_NAMES
            .iter()
            .filter_map(|name| find_table_decl(&parser, name))
            .collect();
        assert!(
            !table_decls.is_empty(),
            "no tree-sitter tables found in {}",
            parser_path.display()
        );

        let raw_dir = out_dir.join(format!("{}_raw_tables", grammar.name));
        fs::create_dir_all(&raw_dir).unwrap();
        dump_raw_tables(
            grammar,
            &parser_path,
            scanner_path.exists().then_some(scanner_path.as_path()),
            &table_decls,
            &raw_dir,
        );

        let compressed_dir = table_root.join(grammar.name);
        fs::create_dir_all(&compressed_dir).unwrap();
        for table_idx in 0..table_decls.len() {
            let table_name = table_decls[table_idx].name.clone();
            let raw_path = raw_dir.join(&table_name);
            let raw = fs::read(&raw_path).unwrap();
            let compressed = compress(&raw);
            let compressed_path = compressed_dir.join(format!("{table_name}.z"));
            fs::write(&compressed_path, compressed).unwrap();

            let static_name = format!(
                "{}_{}",
                grammar.name.to_ascii_uppercase(),
                table_name.to_ascii_uppercase()
            );
            let rel_path = format!("tree_sitter_tables/{}/{table_name}.z", grammar.name);
            generated.push_str(&format!(
                "static {static_name}: PackedTable = PackedTable {{ compressed: include_bytes!(concat!(env!(\"OUT_DIR\"), \"/{rel_path}\")), size: {}, data: OnceLock::new() }};\n",
                raw.len()
            ));
            table_decls[table_idx].size = raw.len();
            packed_tables.push(PackedTable {
                grammar_idx,
                table_idx,
                static_name,
            });
        }
        generated.push('\n');

        let transformed = transform_parser(grammar_idx, &parser, &table_decls, &src_dir);
        let transformed_path = out_dir.join(format!("{}_parser.c", grammar.name));
        fs::write(&transformed_path, transformed).unwrap();
        cc_build.file(&transformed_path);
        if scanner_path.exists() {
            cc_build.file(&scanner_path);
        }

        copy_queries(grammar, &crate_dir, &query_root, &mut generated);
    }

    generated.push_str("#[no_mangle]\npub extern \"C\" fn nnd_tree_sitter_table(grammar: u32, table: u32, size: usize) -> *const c_void {\n    match (grammar, table) {\n");
    for table in &packed_tables {
        generated.push_str(&format!(
            "        ({}, {}) => decode_table(&{}, size),\n",
            table.grammar_idx, table.table_idx, table.static_name
        ));
    }
    generated.push_str("        _ => std::process::abort(),\n    }\n}\n\n");

    for grammar in &grammars {
        let upper = grammar.name.to_ascii_uppercase();
        generated.push_str(&format!(
            "extern \"C\" {{ fn {}() -> *const (); }}\npub fn {}_language() -> Language {{ unsafe {{ LanguageFn::from_raw({}) }}.into() }}\n",
            grammar.function, grammar.name, grammar.function
        ));
        generated.push_str(&format!(
            "pub const {upper}_HIGHLIGHTS_QUERY: &str = include_str!(concat!(env!(\"OUT_DIR\"), \"/tree_sitter_queries/{}_highlights.scm\"));\n",
            grammar.name
        ));
        let injections = query_root.join(format!("{}_injections.scm", grammar.name));
        if injections.exists() {
            generated.push_str(&format!(
                "pub const {upper}_INJECTIONS_QUERY: &str = include_str!(concat!(env!(\"OUT_DIR\"), \"/tree_sitter_queries/{}_injections.scm\"));\n\n",
                grammar.name
            ));
        } else {
            generated.push_str(&format!(
                "pub const {upper}_INJECTIONS_QUERY: &str = \"\";\n\n"
            ));
        }
    }

    fs::write(out_dir.join("tree_sitter_grammars.rs"), generated).unwrap();
    cc_build.compile("nnd_tree_sitter_grammars");
}

fn find_crate_source(package: &str, version: &str) -> PathBuf {
    let dir_name = format!("{package}-{version}");
    let cargo_home = env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| env::var_os("HOME").map(|home| PathBuf::from(home).join(".cargo")))
        .expect("CARGO_HOME or HOME is required to locate tree-sitter grammar sources");
    let registry_src = cargo_home.join("registry/src");

    for entry in fs::read_dir(&registry_src)
        .unwrap_or_else(|_| panic!("failed to read {}", registry_src.display()))
    {
        let path = entry.unwrap().path().join(&dir_name);
        if path.exists() {
            return path;
        }
    }

    panic!("failed to find {dir_name} in {}", registry_src.display());
}

fn find_table_decl(source: &str, name: &str) -> Option<TableDecl> {
    let mut pos = 0;
    while let Some(rel_start) = source[pos..].find("static const ") {
        let start = pos + rel_start;
        let Some(rel_header_end) = source[start..].find("= {") else {
            break;
        };
        let header_end = start + rel_header_end;
        let header = &source[start + "static const ".len()..header_end];
        let needle = format!(" {name}");
        if let Some(name_pos) = header.find(&needle) {
            let after_name = header[name_pos + needle.len()..].trim_start();
            if after_name.starts_with('[') {
                let c_type = header[..name_pos].trim().to_string();
                let open_brace = source[header_end..]
                    .find('{')
                    .map(|i| header_end + i)
                    .unwrap();
                let end = find_initializer_end(source, open_brace);
                return Some(TableDecl {
                    name: name.to_string(),
                    c_type,
                    start,
                    end,
                    size: 0,
                });
            }
        }
        pos = header_end + 1;
    }
    None
}

fn find_initializer_end(source: &str, open_brace: usize) -> usize {
    let bytes = source.as_bytes();
    let mut depth = 0usize;
    let mut i = open_brace;
    while i < bytes.len() {
        match bytes[i] {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    i += 1;
                    while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                        i += 1;
                    }
                    assert_eq!(bytes[i], b';');
                    return i + 1;
                }
            }
            _ => {}
        }
        i += 1;
    }
    panic!("unterminated C initializer");
}

fn dump_raw_tables(
    grammar: &Grammar,
    parser_path: &Path,
    scanner_path: Option<&Path>,
    tables: &[TableDecl],
    raw_dir: &Path,
) {
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let dumper_path = out_dir.join(format!("{}_table_dumper.c", grammar.name));
    let dumper_exe = out_dir.join(format!("{}_table_dumper", grammar.name));

    let mut source = String::new();
    source.push_str("#include <stdint.h>\n#include <stdio.h>\n#include <stdlib.h>\n");
    source.push_str(&format!("#include \"{}\"\n", c_path(parser_path)));
    source.push_str(
        r#"
static void dump_table(const char *dir, const char *name, const void *data, size_t size) {
    char path[4096];
    int n = snprintf(path, sizeof(path), "%s/%s", dir, name);
    if (n < 0 || (size_t)n >= sizeof(path)) abort();
    FILE *file = fopen(path, "wb");
    if (!file) abort();
    if (fwrite(data, 1, size, file) != size) abort();
    if (fclose(file) != 0) abort();
}

#define DUMP_TABLE(name) dump_table(argv[1], #name, name, sizeof(name))

int main(int argc, char **argv) {
    if (argc != 2) return 2;
"#,
    );
    for table in tables {
        source.push_str(&format!("    DUMP_TABLE({});\n", table.name));
    }
    source.push_str("    return 0;\n}\n");
    fs::write(&dumper_path, source).unwrap();

    let mut compile = Command::new(host_cc());
    compile
        .arg("-std=c11")
        .arg("-O0")
        .arg("-w")
        .arg(&dumper_path);
    if let Some(scanner_path) = scanner_path {
        compile.arg(scanner_path);
    }
    compile.arg("-o").arg(&dumper_exe);
    let status = compile
        .status()
        .unwrap_or_else(|e| panic!("failed to run host C compiler: {e}"));
    assert!(
        status.success(),
        "failed to compile table dumper for {}",
        grammar.package
    );

    let status = Command::new(&dumper_exe).arg(raw_dir).status().unwrap();
    assert!(
        status.success(),
        "failed to dump tree-sitter tables for {}",
        grammar.package
    );
}

fn host_cc() -> String {
    if let Ok(cc) = env::var("HOST_CC") {
        return cc;
    }
    if let Ok(host) = env::var("HOST") {
        let key = format!("CC_{}", host.replace('-', "_"));
        if let Ok(cc) = env::var(key) {
            return cc;
        }
    }
    "cc".to_string()
}

fn transform_parser(
    grammar_idx: usize,
    source: &str,
    tables: &[TableDecl],
    src_dir: &Path,
) -> String {
    let header = src_dir.join("tree_sitter/parser.h");
    let mut out = source.to_string();

    let mut tables_sorted = tables.to_vec();
    tables_sorted.sort_by_key(|t| t.start);
    for table in tables_sorted.iter().rev() {
        out.replace_range(
            table.start..table.end,
            &format!("static const {} *{} = NULL;\n", table.c_type, table.name),
        );
    }

    out = out.replacen(
        "#include \"tree_sitter/parser.h\"",
        &format!("#include \"{}\"", c_path(&header)),
        1,
    );

    let loader = make_loader(grammar_idx, tables);
    let insert_pos = out.rfind("#ifdef __cplusplus\nextern \"C\" {").unwrap();
    out.insert_str(insert_pos, &loader);

    out = out.replace("&ts_parse_table[0][0]", "ts_parse_table");
    out = out.replace("&ts_alias_sequences[0][0]", "ts_alias_sequences");
    out = out.replace(
        "&ts_external_scanner_states[0][0]",
        "ts_external_scanner_states",
    );

    out = out.replace(
        "static const TSLanguage language = {",
        "static TSLanguage language;\n  static bool language_initialized = false;\n  if (!language_initialized) {\n    ts_load_compressed_tables();\n    language = (TSLanguage) {",
    );
    let tail = "\n  };\n  return &language;\n}";
    let replacement = "\n    };\n    language_initialized = true;\n  }\n  return &language;\n}";
    let pos = out
        .rfind(tail)
        .expect("failed to find tree-sitter language initializer tail");
    out.replace_range(pos..pos + tail.len(), replacement);

    out
}

fn make_loader(grammar_idx: usize, tables: &[TableDecl]) -> String {
    let mut out = String::new();
    out.push_str("extern const void *nnd_tree_sitter_table(uint32_t grammar, uint32_t table, size_t size);\n\n");
    out.push_str("static void ts_load_compressed_tables(void) {\n");
    out.push_str(&format!("  if ({} != NULL) return;\n", tables[0].name));
    for (table_idx, table) in tables.iter().enumerate() {
        out.push_str(&format!(
            "  {name} = (const {c_type} *)nnd_tree_sitter_table({grammar_idx}, {table_idx}, {size});\n",
            name = table.name,
            c_type = table.c_type,
            size = table.size,
        ));
    }
    out.push_str("}\n\n");
    out
}

fn compress(raw: &[u8]) -> Vec<u8> {
    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::best());
    encoder.write_all(raw).unwrap();
    encoder.finish().unwrap()
}

fn copy_queries(grammar: &Grammar, crate_dir: &Path, query_root: &Path, generated: &mut String) {
    let queries = crate_dir.join("queries");
    let highlights = queries.join("highlights.scm");
    let highlight_out = query_root.join(format!("{}_highlights.scm", grammar.name));
    println!("cargo:rerun-if-changed={}", highlights.display());
    fs::copy(&highlights, &highlight_out).unwrap();

    let injections = queries.join("injections.scm");
    if injections.exists() {
        println!("cargo:rerun-if-changed={}", injections.display());
        fs::copy(
            &injections,
            query_root.join(format!("{}_injections.scm", grammar.name)),
        )
        .unwrap();
    }

    generated.push_str(&format!("// query files copied for {}\n", grammar.package));
}

fn c_path(path: &Path) -> String {
    path.display()
        .to_string()
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
}
