# This script takes care of testing your crate

set -ex

main() {
    cross build --all --target $TARGET
    cross build --all --target $TARGET --release

    if [ ! -z $DISABLE_TESTS ]; then
        return
    fi

    cross test --all --target $TARGET
    cross test --all --target $TARGET --release
}

# we don't run the "test phase" when doing deploys
if [ -z $TRAVIS_TAG ]; then
    main
fi
