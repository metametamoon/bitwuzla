# Bitwuzla for ksmt

This branch keeps the C Bitwuzla that ksmt binds, from upstream commit `1230d80a`, with fixes for lambdas reached through array updates.

`build-linux64.sh` builds the Linux x64 `libbitwuzla.so` that ksmt loads, in Docker, from the checked-out commit.
The library links GMP, libstdc++ and libgcc statically, needs only `libc.so.6` and `libm.so.6`, and refuses to build from a dirty tree.

```shell
BASE_REGISTRY=mirror.gcr.io ./contrib/ksmt/build-linux64.sh out
```

Pushing a tag named `<version>-ksmt.<n>` runs the release workflow, which attaches `libbitwuzla.so` and its sha256 to a GitHub release of that tag.
