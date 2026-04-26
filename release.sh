#!/bin/bash
set -e

# Prerequisites:
#  * `rustup target add x86_64-unknown-linux-musl`
#  * install github CLI (`gh`)
#  * `gh auth login`
#  * `cargo install cargo-about --features=cli`
#  * `cd` to the directory with Cargo.toml etc

COMMIT_MESSAGE=''
TAG_NUM=''
while [[ $# -gt 0 ]]; do
  case $1 in
    -m|--message)
      COMMIT_MESSAGE="$2"
      shift
      shift
      ;;
    --version)
      TAG_NUM="$2"
      shift
      shift
      ;;
    *)
      echo "unknown option: $1"
      exit 1
      ;;
  esac
done

if [ "$COMMIT_MESSAGE" == "" ]
then
    status="$(git status --porcelain)"
    if [ "$status" != "" ]
    then
        echo "uncommitted changes"
        exit 1
    fi
fi

# Pick a version number.

if [ "$TAG_NUM" == "" ]
then
    git fetch origin
    TAG_NUM=`git tag | grep -Po '(?<=^v0\.)\d+$' | sort -n | tail -n1`
    if [ "$TAG_NUM" == "" ]
    then
        echo "couldn't find latest tag number"
        exit 1
    fi
fi
TAG="v0.$TAG_NUM"

NEW_GH_TAG=0
if gh release view $TAG >/dev/null
then
    TAG_NUM=$(($TAG_NUM + 1))
    TAG="v0.$TAG_NUM"
    NEW_GH_TAG=1
fi

if [ "$COMMIT_MESSAGE" == "" ]
then
    COMMIT_MESSAGE="$TAG"
fi

# Write version number to Cargo.toml
BASEDIR=$(dirname "$0")
sed -i.bak "s/^version = \"0\.[0-9]\+\.0\" # \[\[this version number is written by release\.sh\]\]$/version = \"0.$TAG_NUM.0\" # [[this version number is written by release.sh]]/" "$BASEDIR/Cargo.toml" && rm "$BASEDIR/Cargo.toml.bak"

# Pass build time to the env!() in main.rs, passed-through by cargo.
export NND_BUILD_TIME=`date --utc +"%Y-%m-%d %H:%M:%S-%Z"`

# Generate boring legal info. This has to be after updating version number above.
cargo about generate about.hbs -o src/license.rs

# Build in all the modes, with musl and glibc.
for target in "" "--target=x86_64-unknown-linux-musl"
do
    echo "target: $target"
    RUST_BACKTRACE=1 cargo test $target
    for profile in "" "--profile=dbgo" "-r"
    do
        echo "profile: $profile"
        cargo build $target $profile
    done
done

# Commit the version number bump. This is required by crates.io. We usually piggyback it to some useful commit.
git status
git commit -am "$COMMIT_MESSAGE"
git push

# Copy to my machines.

#scp target/x86_64-unknown-linux-musl/dbgo/nnd dev:bin/new-nnd && scp target/x86_64-unknown-linux-musl/release/nnd dev:bin/new-nnd-release && ssh dev 'mv bin/new-nnd bin/nnd; mv bin/new-nnd-release bin/nnd-release;'

cp target/x86_64-unknown-linux-musl/dbgo/nnd ../../nnd-release/nnd-new && mv ../../nnd-release/nnd-new ../../nnd-release/nnd && cp target/x86_64-unknown-linux-musl/release/nnd ../../nnd-release/nnd-release-new && mv ../../nnd-release/nnd-release-new ../../nnd-release/nnd-release
cp target/dbgo/nnd ../../nnd-release/nnd-libc-new && mv ../../nnd-release/nnd-libc-new ../../nnd-release/nnd-libc && cp target/release/nnd ../../nnd-release/nnd-release-libc-new && mv ../../nnd-release/nnd-release-libc-new ../../nnd-release/nnd-release-libc

# Push to itch.
#butler push target/x86_64-unknown-linux-musl/release/nnd al13n/nnd:linux

# Push to github.

cp target/x86_64-unknown-linux-musl/dbgo/nnd nnd-dbgo
trap 'rm nnd-dbgo' EXIT

gh release create "$TAG" --notes "" target/x86_64-unknown-linux-musl/release/nnd nnd-dbgo

rm nnd-dbgo
trap - EXIT

# Push to crates.io
cargo publish

echo "all done!"
