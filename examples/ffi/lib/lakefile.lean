import Lake
open System Lake DSL

package ffi {
  srcDir := "lean"
  precompileModules := true
}

lean_lib FFI

@[defaultTarget] lean_exe test {
  root := `Main
}

target ffi.o (pkg : Package) : FilePath := do
  let oFile := pkg.buildDir / "c" / "ffi.o"
  let srcJob ← inputFile <| pkg.dir / "c" / "ffi.cpp"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
  buildO "ffi.c" oFile srcJob flags "c++"

extern_lib libleanffi (pkg : Package) := do
  let name := nameToStaticLib "leanffi"
  let ffiO ← fetch <| pkg.target ``ffi.o
  buildStaticLib (pkg.buildDir / "c" / name) #[ffiO]
