use crate::{error::*, terminal::*, log::*};
use std::{io, io::Write};

pub fn print_help_chapter(arg: &str, executable_name: &str) -> bool {
    match arg {
        "--help" => println!(r###"Hi, I'm a debugger.

Please (pretty please!) report all bugs, usability issues, slowness, first impressions, improvement ideas, feature requests, etc.
Create an issue at https://github.com/al13n321/nnd/issues or send an email to mk.al13n+nnd@gmail.com

Usage:
{0} command [args...]   - run a program under the debugger (i.e. just prepend {0} to the command line)
sudo {0} -p pid   - attach to an existing process
{0} -c core_dump_path [executable_path]   - open core dump; -o flag (see below) is recommended if the core was produced on a different machine (with different version of libc than available locally)
{0} --dump-core [--mode=direct|live|fork] -p pid > out   - instead of running the debugger, make a core dump snapshot of a running program, similar to gdump

Additional arguments:
--stdin/--stdout/--stderr path   - redirect stdin/stdout/stderr to file
--tty path   - redirect both stdin and stdout to path, see --help-tty
-s   - stop on main() (only applies to the first time the program starts; when starting it again from UI, press 'step' key instead of 'run' to stop on main())
-S   - stop early in process startup sequence (long before main(), but after loading dynamic libraries)
-d path   - directory in which to look for source code; if specified multiple times, multiple directories will be searched; default: current directory
--module path   - path to executable or dynamic library from which to load debug symbols; useful if the running executable is stripped and you have an unstripped version on the side; can be specified multiple times to provide multiple dynamic libraries (they'll be automatically matched by build id)
-o   - try to get debug info from debuginfod server at https://debuginfod.elfutils.org/ ; alternatively, set environment variable DEBUGINFOD_URLS to a space-separated list of URLs to use
--mouse full|no-hover|disabled   - mouse mode; 'no-hover' to react only to clicking and dragging, 'disabled' to disable mouse altogether; default is 'full' (if it doesn't work, check if mouse reporting is enabled in the terminal application)
-n name   - session name, to identify saved state like open files and breakpoints; "-" for temporary session that doesn't save state; "--" to avoid touching any files at all (at ~/.nnd/)
--breakpoint path:line   - set a breakpoint at the specified source file and line number (e.g. src/main.c:42); repeat the parameter to set multiple breakpoints; the path must exactly match a path appearing in debug info
--help   - show this help message; see below for more help pages

Documentation chapters:
--help-overview - general information and first steps, start here
--help-known-problems - list of known bugs and missing features to look out for
--help-watches - watch expression language documentation
--help-files - files in ~/.nnd/ - keys config, log file, default stdout/stderr redirects, saved state
--help-tty - how to debug interactive programs that require a terminal (e.g. using this debugger to debug itself)
--help-features - raw list of features (not very readable)"###,
                             executable_name),
        "--help-overview" => println!(r###"nnd is a debugger that has a TUI and is meant to be fast and enjoyable to use, and work well on large executables.
('nnd' stands for 'no-nonsense debugger', but it doesn't quite live up to this name at the moment)

Limitations:
 * Linux only
 * x86 only
 * 64-bit only
 * TUI only (no REPL, no GUI)
 * no remote debugging (but works fine over ssh)
 * single process (doesn't follow forks)
 * no record-replay or other backwards stepping

Properties:
 * Not based on gdb or lldb, implemented mostly from scratch.
   (Uses libraries for a few well-isolated things like disassembling, DWARF parsing, and demangling.)
   (Many tricky things are handcrafted, e.g.: stepping (and dealing with inlined functions), breakpoints (and switching between hw/sw breakpoints as needed to make things work),
    debug info handling (data structures, parallel loading), type system (parallel loading and deduplication), watch expression interpreter, all of UI.)
 * Fast.
   Operations that can be instantaneous should be instantaneous. I.e. snappy UI, no random freezes, no long waits.
   (Known exception: if the program has >~2k threads things become pretty slow, can be improved.)
   Operations that can't be instantaneous (e.g. loading debug info) should be reasonably efficient, multi-threaded, asynchronous, cancellable, and have progress bars.
 * Works on large executables (tested mostly on 2.5 GB clickhouse).
 * Reasonably careful error reporting.

# Getting started

When running the debugger for the first time, notice:
 1. The UI consists of windows. There's an 'active' window, indicated with bright outline.
    The active window can be selected using digit keys (window numbers are shown in their titles), or using alt+arrows, or with the mouse.
 2. The 'controls' window in top left lists (almost) all available key combinations.
    Some of them are global, others depend on the active window.
 3. Press control-q to quit.

This information should be enough to discover most features by trial and error, which is recommended. Additionally, reading --help-known-problems and --help-watches is recommended.

UI tips:
 * Not compatible with Mac OS default Terminal application. Use e.g. iTerm2 or kitty instead. (Only relevant when ssh'd to a Linux machine, since the debugger doesn't support running on Mac OS.)
 * There's mouse support. If it's not working, check if mouse reporting is enabled in the terminal application settings.
 * When mouse is enabled, click+dragging usually doesn't select text (to copy it out of the terminal). But terminal applications usually have a way to override this and select text anyway.
   Try shift+drag (in GNOME Terminal or kitty) or option+drag (in iTerm2).
 * In 'controls' window, prefix "C-" means ctrl key, "M-" means alt/option, "S-" means shift.
   On Mac OS you may need to change terminal settings to make the option key work, e.g. in kitty set "macos_option_as_alt both".
   Key bindings can be changed through config file, see --help-files
 * If you use tmux, the escape key is unreliable, consider using ctrl-g instead. Tmux adds 0.5s delay before passing the escape key through, and if you press another key during that time,
   the two key presses get incorrectly interpreted as alt+keypress (that's how ansi escape codes work, unfortunately).
 * Windows can be resized by dragging the boundaries with the mouse. Rearranging windows is not implemented yet.
 * Press 'tab' to open a tooltip. Supported in tables (binaries, stack, etc) and watches window. Useful for copying long values or paths, and might contain additional information. Also available in search dialogs.

Debugging tips:
 * The highlighted characters in the source code window are locations of statements and inlined function calls, as listed in the debug info.
   These are all the places where the control can stop, e.g. if you step repeatedly or add a breakpoint.
 * 'Step over column' ('m' key) runs until the control moves to a different line+column location. Similar to how 'step over line' runs until the control moves to a different line.
   Useful for stepping into a function call when its arguments are nontrivial expressions - you'd do step-over-column to skip over evaluating the arguments,
   then step-into when the current column is at the function call you're interested in.
   (Is there a way to put a breakpoint on a column? Not directly, but you can put breakpoint on the disassembly instruction corresponding to the column. Find it by cycling through line's disassembly locations by pressing '.'/',' in code window.)
 * Steps are stack-frame-dependent: step-out steps out of the *currently selected* stack frame (as seen in the threads window on the right), not the innermost stack frame.
   Step-over steps over the calls inside the currently selected stack frame, i.e. it may involve an internal step-out.
   (This may seem like an unnecessary feature, but if you think through how stepping interacts with inlined functions, it's pretty much required, things get very confusing otherwise.)
 * While a step is in progress, breakpoints are automatically disabled for the duration of the step.
 * Stepping can be interrupted with the suspend key ('p' key). Useful e.g. if you try to step-over a function, but the function turns out to run forever.
 * Run-to-cursor works like a step: it runs until the selected (not any) thread hits the requested line, and it disables other breakpoints for the duration of the step.
 * To start the program and run to start of main(), press step-into ('s' key) when the program is not running (e.g. after killing it with 'C-k' key).
 * Step-into-instruction ('S' key) works no matter what, even if there's no debug info or if disassembly or stack unwinding fails. Use it when other steps fail.
 * Breakpoints are preserved across debugger restarts, but they're put into disabled state on startup. Use Enter key in breakpoints window to reactivate.
 * To make a conditional breakpoint, press M-enter on a regular breakpoint and edit the condition expression (in breakpoints window).
   Conditional breakpoint stops the program if the condition expression evaluates to nonzero or fails to evaluate.
   If you don't want to stop on evaluation error, wrap the expression in 'try(...)' (it returns 0 on if evaluation failed for any reason).
   E.g.: 'try(abstract_class_ptr.concrete_class_field)' will stop only if abstract_class_ptr was auto-downcast to a class that has the given field, and the field is nonzero.
 * The function search (in disassembly window, 'o' key) currently does fuzzy search over *mangled* function names, for peformance reasons.
   The search results display demangled names, i.e. slightly different from what's actually searched. Press tab to see mangled name.
 * In watches window, on non-root tree nodes press Enter to add a corresponding watch. E.g. for local variable or struct field or array element.
 * Expect debugger's memory usage around 3x the size of the executable. E.g. ~7 GB for 2.3 GB clickhouse, release build. This is mostly debug information.
   (If you're curious, see ~/.nnd/<number>/log for a breakdown of which parts of the debug info take how much memory and take how long to load.)
 * For clickhouse server, use CLICKHOUSE_WATCHDOG_ENABLE=0. Otherwise it forks on startup, and the debugger doesn't follow forks.

Please (pretty please!) report all bugs, usability issues, slowness, first impressions, improvement ideas, feature requests, etc.
Create an issue at https://github.com/al13n321/nnd/issues or send an email to mk.al13n+nnd@gmail.com"###),
        "--help-known-problems" =>             println!(r###"Current limitations:
 * Thread filter ('/' in the threads window) is too limited: just a substring match in function name, file name, and thread name. Need to extend it enough to be able to e.g. filter out idle threads waiting for work or epoll.
 * In watch expressions, type names (for casts or type info) have to be spelled *exactly* the same way as they appear in the debug info.
   E.g. `std::vector<int>` doesn't work, you have to write `std::__1::vector<int, std::__1::allocator<int> >` (whitespace matters).
   The plan is to add a fuzzy search dialog for type names, similar to file and function search.
   (There is no plan to actually parse the template type names into their component parts; doing it correctly would be crazy complicated like everything else in C++.)
 * No custom pretty-printers, only the built-in ones for C++ and Rust standard libraries.
 * Can't assign to the debugged program's variables or registers.
 * No data breakpoints, whole-file breakpoints, special breakpoints (signals, exceptions/panics, except for always-on stop on fatal signals). But for exceptions or panics you can set breakpoint manually: in disassembly window press 'o' to search for function, find __cxa_throw or rustc_panic, and put a breakpoint at the start.
 * Conditional breakpoints are not super fast: a few thousand evaluations per second.
 * Inside libraries that were dlopen()ed at runtime, breakpoints get disabled on program restart. Manually disable-enable the breakpoint after the dlopen() to reactivate it.
 * The disassembly window can only open functions that appear in .symtab or debug info. Can't disassemble arbitrary memory, e.g. JIT-generated code or code from binaries without .symtab or debug info.
 * The debugger gets noticeably slow when the program has > 1K threads, and unusably slow with 20K threads. Part of it is inevitable syscalls
   (to start/stop all n threads we have to do n*const syscalls, then wait for n notifications - that takes a while), but there's a lot of room for improvement anyway
   (reduce the const, do the syscalls in parallel, avoid the remaining O(n^2) work on our side).
 * No customization of colors. Dark theme only.
 * No remote debugging. You can use the debugger over ssh, but it can be inconvenient for production servers: you have to scp the source code and the unstripped binary to it.
   And the debugger uses lots of RAM, which may be a problem on small servers.
   (I'm not sure what exactly to do about this. Fully separating the debugger-agent from UI+debuginfo would increase the code complexity a lot and make performance worse.
    Maybe I'll instead run the ~whole debugger on the server and have a thin client that just streams the rendered 'image' (text) from the server and sends the source code files on demand.
    This removes the need to scp the source code to the server, but leaves all the other problems.)"###),
        "--help-watches" => println!(r###"In the watches window, you can enter expressions to be evaluated. It uses a custom scripting language, documented here.

Currently the language has no loops or conditionals, just expressions. The syntax is C-like/Rust-like.

(Throughout this document, single quotes '' denote example watch expressions. The quotes themselves are not part of the expression.)

General info:
 * Can access the debugged program's local variables (as seen in the locals window), global variables (including thread-locals and static variables in functions), and registers: 'my_local_var', 'rdi'.
   If a local variable is not found, it's probably optimized out. Fields of 'this' are accessible as 'this.my_field', not 'my_field'.
 * Has basic C-like things you'd expect: arithmetic and logical operators, literals, array indexing, pointer arithmetic, '&x' to take address, '*x' to dereference.
 * Type cast: 'p as *u8'. Casts are very permissive, ~any value can be reinterpreted as ~any type.
 * Field access: 'my_struct.my_field'. Pointers are auto-dereferenced: 'my_ptr.my_field'. There's no '->' operator.
 * Fields can also be accessed by index: 'my_struct.3' (useful when field names are empty or duplicate).
 * 'p.[n]' to turn pointer 'p' to array of length 'n'. E.g. 'my_string.ptr.[my_string.len]'.
 * 'begin..end' to turn a pair of pointers to the array [begin, end). E.g. 'my_vector.begin..my_vector.end'.
 * '^x' looks for variable x in all stack frames.
 * 'var(x)' shows additional information about variable x, e.g. its declaration site.

Gotchas:
 * 'var(x)' and 'type(t)'/'typeof(x)' show variable/type declaration site (if present in debug info). Press enter on it (or click) to open in code window.
 * If a variable has the same name as a register, use `` to refer to the variable: '`rax`'.
 * If a global variable has the same name as a local variable, use :: prefix to refer to the global variable: '::foo'.
 * Currently only fully-qualified type names and global variable names are recognized.
 * Currently types and global variables nested inside functions are difficult to access. The recognized "fully-qualified" name has a "_" instead of the function name.
   Use variable search (watches window, 'o' key); optionally, start the query with '@' to search by filename, add ":<number>" to filter by line number.
 * Be careful with operator precedence when combining casts and pointer arithmetic (casts have higher precedence):
   'offset + (my_u64_ptr as *u8)' and 'offset + my_u64_ptr as *u8' produce different result.

Types:
 * Can access the types from the debugged program's debug info (structs, classes, enums, unions, primitive types, etc) and typedefs.
 * Common primitive types are also always available by the following names: void, u8, u16, u32, u64, i8, i16, i32, i64, f32, f64, char8, char32, bool.
 * '* MyType' (without quotes) is pointer to MyType.
 * '[MyType; 100]' is array of 100 MyType-s.
 * '[MyType]' is an array of unknown length of MyType-s. Useful for casting simd registers: 'ymm3 as [u16]' (equivalent to 'ymm as [u16; 16]'), or other values: 'my_struct as [u64]'.
 * 'char8' and arrays of 'char8' are shown as strings (UTF8), 'u8'/'i8' and their arrays are shown as numbers. Cast between them if needed,
   e.g. 'my_array as [char8]' to show as string, 'my_string as [u8]' to show as numbers.

Inspecting types:
 * 'type(<name>)' to get information about a type, e.g. 'type(DB::Chunk)' - contains things like size and field offsets.
 * Use backticks to escape type names with templates or weird characters: 'type(`std::__1::atomic<int>`)'
   E.g. '`std::__1::atomic<int>`' works (on some version of libc++), but '`std::__1::atomic<int32_t>`', '`std::atomic<int>`', and '`atomic<int>`' don't.
 * 'typeof(<expression>)' to get information about result type of an expression.
   (Currently the expression is partially evaluated in some cases, e.g. 'typeof(*(0 as *mystruct))' works, but 'typeof((0 as *mystruct).myfield)' doesn't.)

Script variables:
 * 'x=foo.bar.baz' to assign to a new script variable 'x', which can then be used by later watch expressions.
 * Can't assign to the debugged program's variables. Script variables live in the debugger, outside the debugged program.
 * Watch expressions are evaluated in order from top to bottom.
   Watches lower down the list can use script variables assigned above.
 * Values are held by reference when possible. E.g. '&x' works after 'x=foo.bar', but not after 'x=1'.
 * No scopes, all script variables are global.
 * If the debugged program has a variable with the same name, it can be accessed with backticks: '`x`', while the script variable can be accessed without backticks: 'x'

Pretty-printers:
 * "Pretty-printers" are actually not printers, they're transformations that turn values into other values, which may then be printed using normal printers.
   E.g. an std::map is turned into an array of pairs.
 * If a struct has exactly one nonempty field, we replace the struct with the value of that field.
   Useful for trivial wrappers that are ubiquitous in C++ and Rust.
   E.g. unwraps std::unique_ptr into a plain pointer, even though it actually has multiple levels of wrappers, inheritance, and empty fields.
 * Abstract classes are automatically downcasted to concrete ones. Applies to any class/struct with a vtable pointer.
   Not very reliable, currently it often fails when the concrete type is template or is in anonymous namespace.
   (This can be improved to some extent, but can't be made fully reliable because vtable information is poorly structured in DWARF/symtab.)
 * Fields of base classes are inlined. Otherwise the base class is a field named '#base'.
 * There are designated pretty-printers for most C++ and Rust containers. If some container is not pretty-printed, maybe you're using libstdc++/libc++ version
   newer or older than mine - please report and I'll probably make pretty-printers work for it too.
 * Currently no support for custom pretty-printers.
 * All of the above transformations can be disabled by adding ".#r" to the expression.
 * Pretty-printers apply to intermediate values as well. E.g. 'my_vector[42]' uses a pretty-printer to turn the vector into array before applying the [] operator to it;
   to access fields of the original struct, use #r: 'my_vector.#r.__M_begin'.

Value modifiers:
 * 'value.#x' to print in hexadecimal. Affects numbers, strings, and byte arrays.
 * 'value.#b' to print in binary.
 * 'value.#r' to disable pretty-printers.
   This applies both to how the value is printed and to field access:
   'foo.bar' will access field 'bar' of the transformed 'foo', i.e. after unwrapping single-field structs, downcasting to concrete type, and inlining base class fields.
   'foo.#r.bar' will access field 'bar' of 'foo' verbatim.
 * Modifiers propagate to descendants. E.g. 'my_struct.#x' will print all struct's fields as hexadecimal.
 * Modifiers propagate through most operations. E.g. 'my_array.#x as [u8]' is the same as '(my_array as [u8]).#x'.
 * 'value.#p' is the opposite of '.#r'. Can be useful with field access: 'my_struct.#r.my_field.#p' re-enables pretty-printing after disabling it to access a raw field."###),
        "--help-files" => println!(r###"The debugger creates directory ~/.nnd/ and stores a few things there, such as log file and saved state (watches, breakpoints, open tabs).
It doesn't create any other files or make any other changes to your system.

Key bindings can be customized by creating ~/.nnd/keys . Read the comments in ~/.nnd/keys.default to get started.

Things like watches, breakpoints, open files, etc persist when closing and reopening the debugger. Such state is associated with a "session" and is saved at '~/.nnd/<session-name>/state'.
Each session can have at most one debugger process running at any given time (synchronized by '~/.nnd/<session-name>/lock').
The session directory also contains these files:
 * 'stdout', 'stderr' - redirected stdout and stderr of the debugged program, unless overridden with --stdout/--stderr/--tty.
   (stdin is redirected to /dev/null by default.)
 * 'log' - some messages from the debugger itself. Sometimes useful for debugging the debugger. Sometimes there are useful stats about debug info.
   On crash, error message and stack trace go to this file. Please include this file when reporting bugs, especially crashes.

On startup, the debugger picks the session-name to use, which can be controlled using `--session` (aka `-n`) command line argument:
 * If --session=name is provided, this name is used (with prefix "sess-" prepended to avoid name collisions with non-session files).
 * If no --session is provided, a numeric session-name is picked automatically. When only one nnd is started, it'll use '~/.nnd/0'. If a second nnd is started while the first is still running, it'll get '~/.nnd/1/', etc.
   After an nnd process exits, the directory can be reused.
   E.g. if you start a few instances of nnd, then quit them all, then start them again in the same order, they'll reuse the same sessions in the same order.
 * If --session=-, a "temporary" session is used, named "temp-<number>". The only difference from default mode is that state is not saved.
 * If --session=--, the debugger won't touch any files at all (won't create `~/.nnd` etc). The debugged program's stdout and stderr are redirected to /dev/null. The log file is not written.

Session directory path is shown in UI in the status window (on the left).

When using `sudo nnd -p`, keep in mind that the ~/.nnd` will be in the home directory of the root user, not the current user."###),
        "--help-tty" => println!(r###"The debugger occupies the whole terminal with its TUI. But what if the debugged program also wants to use the terminal in an interactive way?
E.g. how to use nnd to debug itself?

One way is to just attach using -p <pid>.

But what if you need to set breakpoints before the program starts, e.g. to debug a crash on startup? Then you can do the following:
 1. Open a terminal window (in terminal application or tmux or whatever). Let's call this window A. This is where you'll be able interact with the debugged program.
 2. This terminal window is attached to some 'pty' pseudo-device in /dev/pts/ . Figure out which one:
     $ ls -l /proc/$$/fd | grep /dev/pts/
    For example, suppose this outputs /dev/pts/2 . You can also double-check this with: `echo henlo > /dev/pts/2` - if the text appears in the correct terminal then it's the correct path.
 3. Pacify the shell in this terminal window (to prevent it from eating input):
     $ sleep 1000000000
 4. In another terminal window (B) run the debugger:
     $ nnd --tty /dev/pts/2 the_program_to_debug
 5. Now you have the debugger running in window B while the debugged program inhabits the terminal in window A
    (which will come to life when you resume the program in the debugger, `sleep` notwithstanding).

The latter approach is often more convenient than -p, even when both approaches are viable.

(This can even be chained multiple levels deep: `nnd --tty /dev/pts/1 nnd --tty /dev/pts/2 my_program`. The longest chain I've used in practice is 4 nnd-s + 1 other program.)"###),
        "--help-features" => println!(r###"Appendix: raw list of features (optional reading) (a little outdated)

loading debug info
  progress bar in the binaries window (top right)
  multithreaded, reasonably fast
  debugger is functional while debug info is loading, but there won't be line numbers or function names, etc
  after debug info is loaded, everything is automatically refreshed, so things like function names and source code appear
  supports DWARF 4 and 5, debuglink, compressed ELF sections
threads window (bottom right)
  color tells the stop reason
  search
    not fuzzy
    matches function name and file name
stack trace window (right)
  when switching frame, jumps to the location in disassembly and source code
source code window (bottom)
  makes some attempts to guess the correct path, if it doesn't match between the debug info and the local filesystem
  file search
    fuzzy
    only sees files mentioned in the debug info
  shows statements and inlined calls
  scrolls disassembly window when moving cursor
    can cycle through locations if multiple
    prioritizes locations close to disassembly window cursor
  breakpoints
  shows URL for rust standard library files
stepping
  into-instruction, into-line, over-instruction, over-line, over-column (useful for function arguments), out of inlined function, out of real function
  aware of inlined functions
  frame-dependent (e.g. step-out steps out of the selected stack frame, not the top stack frame; similar for step-over)
    disables breakpoints for the duration of the step
disassembly window (top)
  shows inlined functions
  scrolls source window when moving cursor
    can change inline depth
  function search
    fuzzy
    mangled :(
    shows file:line
  shows breakpoint locations (for breakpoints added in the source code window)
watches, locals, registers (bottom left)
  tree
  automatic downcasting of virtual classes to the most concrete type
  expression language (see --help-watches)
breakpoints (top right, second tab)
  aware of inlined functions
  can be disabled
  jump to location when selecting in the breakpoints window
  shows adjusted line
autosaving/restoring state
  see --help-files
obscure feature: locations window
  tells where each variable lives (register, memory location, expression, etc) (actually it just prints the DWARF expression)
  for selected disassembly line
secret feature: C-p for self-profiler
secret feature: C-l to drop caches and redraw
removing breakpoints on exit
  if the debugger is attached with -p, and some breakpoints are active, it's an important job of the debugger to deactivate all breakpoints when detaching
  otherwise the detached process will get SIGTRAP and crash as soon as it hits one of the leftover breakpoints
  nnd correctly removes breakpoints when exiting normally, or exiting with an error, or exiting with a panic (e.g. failed assert)
  but it doesn't remove breakpoints if the debugger receives a fatal signal (e.g. SIGSEGV or SIGKILL)"###),
        _ => return false,
    }
    true
}

pub fn run_input_echo_tool() -> Result<()> {
    let _restorer = TerminalRestorer;
    configure_terminal(MouseMode::Disabled)?;

    let mut reader = InputReader::new();
    let mut keys: Vec<KeyEx> = Vec::new();
    let mut prof = ProfileBucket::invalid();
    let mut commands: Vec<u8> = Vec::new();
    loop {
        // Read keys.
        let mut evs: Vec<Event> = Vec::new();
        reader.read(&mut evs, &mut prof)?;

        // Exit on 'q'.
        for ev in evs {
            if let Event::Key(key) = ev {
                if key.key == Key::Char('q') && key.mods.is_empty() {
                    return Ok(());
                }
                keys.push(key);
            }
        }
        if keys.len() > 200 {
            keys.drain(..keys.len()-200);
        }

        // Render.
        commands.clear();
        write!(commands, "{}\x1B[{};{}H{}", CURSOR_HIDE, 1, 1, "input echo tool; press some keys, and their names will show up here, in a format suitable for the keys config file").unwrap();
        write!(commands, "\x1B[{};{}H{}", 2, 1, "some key combinations are indistinguishable due to ANSI escape codes, e.g. ctrl-j and enter").unwrap();
        write!(commands, "\x1B[{};{}H{}", 3, 1, "press 'q' to exit").unwrap();
        for (y, key) in keys.iter().rev().enumerate() {
            write!(commands, "\x1B[{};{}H\x1B[K{}", y + 4 + 1, 1, key).unwrap();
        }

        // Output.
        io::stdout().write_all(&commands)?;
        io::stdout().flush()?;

        // Wait for input.
        let mut pfd = libc::pollfd {fd: libc::STDIN_FILENO, events: libc::POLLIN, revents: 0};
        unsafe {libc::poll(&mut pfd as *mut libc::pollfd, 1, -1)};
    }
}
