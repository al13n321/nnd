RUST_BACKTRACE=1 cargo test && cargo build --profile dbgo && cargo build -r && scp target/x86_64-unknown-linux-musl/dbgo/nnd dev:bin/new-nnd && ssh dev 'mv bin/new-nnd bin/nnd' && cp target/x86_64-unknown-linux-musl/release/nnd ../../nnd-release/nnd-new && mv ../../nnd-release/nnd-new ../../nnd-release/nnd