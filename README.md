This is a modified version of Dafny that can export the Dafny program as an
Isabelle expression and use a modified Boogie version.
The translation is also modified.

# Setup

You may need to remove the `BPL_EXPORT_DIR_OPTION` at the beginning of
[DafnyDriver.cs](./Source/DafnyDriver/DafnyDriver.cs).
The Boogie version in [Directory.Build.props](./Source/Directory.Build.props)
must be set to the same version used by the modified Boogie nuget package.

[Installation instructions](https://github.com/dafny-lang/dafny/wiki/INSTALL)

# Example

```sh
dafny /fragment /compile:0 /print:foo.bpl /exportDfy:foo_export foo.dfy
```
