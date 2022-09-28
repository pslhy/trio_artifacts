# Artifacts for "Inductive Synthesis of Structurally Recursive Functional Programs from Non-Recursive Expressions

##Build
```
$ git clone https://github.com/pslhy/trio_artifacts.git
$ cd trio_artifacts
$ . setenv # or ($ bash setenv)
$ make
```

## run example
option -print-data prints Solution Size and CEGIS Iter times.
```
$ burst/BurstCmdLine.exe -use-trio benchmark/io_basic/list_append.mls

$ burst/BurstCmdLine.exe -print-data -use-trio benchmark/ref_basic/list_fold.mls
```
