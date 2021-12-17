/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.Build.Targets
import Lake.Build.Actions
import Lake.Build.Recursive
import Lake.Build.TargetTypes
import Lake.Config.Package

open System
open Lean hiding SearchPath

namespace Lake

-- # Info

/-- A module of a known Lake package. -/
structure Module where
  pkg : Package
  name : Name
  deriving Inhabited

class ToModule (α : Type u) where
  toModule : α → Module

export ToModule (toModule)

namespace Module

@[inline] def srcFile (self : Module) : FilePath :=
  self.pkg.modToSrc self.name

@[inline] def oleanFile (self : Module) : FilePath :=
  self.pkg.modToOlean self.name

@[inline] def cFile (self : Module) : FilePath :=
  self.pkg.modToC self.name

@[inline] def traceFile (self : Module) : FilePath :=
  self.pkg.modToTraceFile self.name

end Module

/-- A build facet of a `Module`. -/
structure ModuleFacet where
  module : Module
  facet : Name
  deriving Inhabited

instance : ToModule ModuleFacet := ⟨(·.module)⟩

@[inline] def ModuleFacet.pkg (self : ModuleFacet) :=
  self.module.pkg

/-- A `ModuleFacet` known at type-level. -/
structure StaticModuleFacet (facet : Name) extends ModuleFacet where
  facet_eq : toModuleFacet.facet = facet

instance : ToModule (StaticModuleFacet f) := ⟨(·.module)⟩

def StaticModuleFacet.mk' {facet : Name} (mod : Module) : StaticModuleFacet facet :=
  {module := mod, facet, facet_eq := rfl}

instance : CoeTail Module (StaticModuleFacet f) := ⟨StaticModuleFacet.mk'⟩
instance : Inhabited (StaticModuleFacet f) := ⟨StaticModuleFacet.mk' Inhabited.default⟩

/-- The`.lean` source file facet of a module. -/
abbrev LeanSrc := StaticModuleFacet `lean.src

@[inline] def Module.src (self : Module) : LeanSrc :=
  self

@[inline] def LeanSrc.file (self : LeanSrc) : FilePath :=
  self.module.srcFile

instance : GetMTime LeanSrc := ⟨fun x => getMTime x.file⟩
instance : ComputeHash LeanSrc IO := ⟨fun x => computeHash x.file⟩
instance : CheckExists LeanSrc := ⟨fun x => checkExists x.file⟩

/-- The `.olean` file facet of a module. -/
abbrev Olean :=  StaticModuleFacet `olean

@[inline] def Module.olean (self : Module) : Olean :=
  self

@[inline] def Olean.file (self : Olean) : FilePath :=
  self.module.oleanFile

instance : GetMTime Olean := ⟨fun x => getMTime x.file⟩
instance : ComputeHash Olean IO := ⟨fun x => computeHash x.file⟩
instance : CheckExists Olean := ⟨fun x => checkExists x.file⟩

/-- The Lean-emitted `.c` file facet of a module. -/
abbrev LeanC := StaticModuleFacet `lean.c

@[inline] def Module.c (self : Module) : LeanC :=
  self

@[inline] def LeanC.file (self : LeanC) : FilePath :=
  self.module.cFile

/-- The combined `.olean` and `.c` facet of a module. -/
abbrev OleanAndC := StaticModuleFacet `oleanAndC

@[inline] def Module.oleanAndC (self : Module) : OleanAndC :=
  self

namespace OleanAndC

@[inline] def olean (self : OleanAndC) :=
  self.module.olean

@[inline] def c (self : OleanAndC) :=
  self.module.c

protected def getMTime (self : OleanAndC) : IO MTime := do
  return mixTrace (← getMTime self.olean.file) (← getMTime self.c.file)

instance : GetMTime OleanAndC := ⟨OleanAndC.getMTime⟩

protected def computeHash (self : OleanAndC) : IO Hash := do
  return mixTrace (← computeHash self.olean.file) (← computeHash self.c.file)

instance : ComputeHash OleanAndC IO := ⟨OleanAndC.computeHash⟩

protected def checkExists (self : OleanAndC) : BaseIO Bool := do
  return (← checkExists self.olean.file) && (← checkExists self.c.file)

instance : CheckExists OleanAndC := ⟨OleanAndC.checkExists⟩

end OleanAndC

-- #  Target Definitions

abbrev OleanTarget := BuildTarget Olean
abbrev ActiveOleanTarget := ActiveBuildTarget Olean

abbrev LeanCTarget := BuildTarget LeanC
abbrev ActiveLeanCTarget := ActiveBuildTarget LeanC

abbrev OleanAndCTarget := BuildTarget OleanAndC

namespace OleanAndCTarget

@[inline] def module (self : OleanAndCTarget) : Module :=
  self.info.module

@[inline] def olean (self : OleanAndCTarget) : Olean :=
  self.module.olean

def oleanTarget (self : OleanAndCTarget) : OleanTarget :=
  Target.mk self.olean do self.bindSync fun i _ => computeTrace i.olean.file

@[inline] def c (self : OleanAndCTarget) : LeanC :=
  self.module.c

def cTarget (self : OleanAndCTarget) : LeanCTarget :=
  Target.mk self.c do self.bindSync fun i _ => computeTrace i.c.file

def cFileTarget (self : OleanAndCTarget) : FileTarget :=
  Target.mk self.c.file do self.bindSync fun i _ => computeTrace i.c.file

end OleanAndCTarget

structure ActiveOleanAndCTargets where
  oleanTarget : ActiveOleanTarget
  cTarget : ActiveLeanCTarget
  deriving Inhabited

namespace ActiveOleanAndCTargets
@[inline] def olean (self : ActiveOleanAndCTargets) := self.oleanTarget.info
@[inline] def c (self : ActiveOleanAndCTargets) := self.cTarget.info
end ActiveOleanAndCTargets

/--
An active module `.olean` and `.c` target consists of a single task that
builds both with two dependent targets that compute their individual traces.
-/
abbrev ActiveOleanAndCTarget := ActiveBuildTarget ActiveOleanAndCTargets

namespace ActiveOleanAndCTarget

@[inline] def olean (self : ActiveOleanAndCTarget) := self.info.olean
@[inline] def oleanTarget (self : ActiveOleanAndCTarget) := self.info.oleanTarget

@[inline] def c (self : ActiveOleanAndCTarget) := self.info.c
@[inline] def cTarget (self : ActiveOleanAndCTarget) := self.info.cTarget
@[inline] def cFileTarget (self : ActiveOleanAndCTarget) :=
  self.info.cTarget.withInfo self.info.c.file

end ActiveOleanAndCTarget

def OleanAndCTarget.activate (self : OleanAndCTarget) : BuildM ActiveOleanAndCTarget := do
  let t ← BuildTarget.activate self
  let oleanTask ← t.bindSync fun info depTrace => do
    return mixTrace (← computeTrace info.olean.file) depTrace
  let cTask ← t.bindSync fun info _ => do
    return mixTrace (← computeTrace info.c.file) (← getLeanTrace)
  return t.withInfo {
    oleanTarget := ActiveTarget.mk self.olean oleanTask
    cTarget := ActiveTarget.mk self.c cTask
  }

-- # Target Builders

@[inline] def computeModuleTrace
(mod : Module) (depTrace : BuildTrace) : BuildM BuildTrace := do
  let srcTrace : BuildTrace ← computeTrace mod.src
  (← getLeanTrace).mix <| srcTrace.mix depTrace

@[inline] def buildModuleUnlessUpToDate
[CheckExists i] [GetMTime i] [ToModule i] (info : i)
(depTrace : BuildTrace) (build : BuildM PUnit) : BuildM PUnit := do
  let mod := toModule info
  let modTrace ← computeModuleTrace mod depTrace
  buildUnlessUpToDate info modTrace mod.traceFile build

/--
Build the `.olean` and `.c` files for just a single module
(and not its transitive dependencies).
-/
def OleanAndC.build1 (self : OleanAndC) (depTrace : BuildTrace) : BuildM PUnit := do
  buildModuleUnlessUpToDate self depTrace do
    compileOleanAndC self.module.src.file self.olean.file self.c.file
      (← getOleanPath) self.pkg.rootDir self.pkg.moreLeanArgs (← getLean)

def moduleOleanAndCTargetOnly (mod : Module) (depTarget : BuildTarget x) : OleanAndCTarget :=
  Target.mk mod.oleanAndC <| depTarget.bindOpaqueSync fun depTrace => do
    mod.oleanAndC.build1 depTrace; depTrace

/--
Build just the `.olean` file for the single module
(and not its transitive dependencies).
-/
def Olean.build1 (self : Olean) (depTrace : BuildTrace) : BuildM BuildTrace := do
  buildModuleUnlessUpToDate self depTrace do
    compileOlean self.module.src.file self.file
      (← getOleanPath) self.pkg.rootDir self.pkg.moreLeanArgs (← getLean)
  return mixTrace (← computeTrace self) depTrace

-- # Recursive Building

/-
Produces a recursive module target builder that
builds the target module after recursively building its local imports
(relative to the workspace).
-/
def recBuildModuleWithLocalImports
[Monad m] [MonadLiftT BuildM m] [MonadFunctorT BuildM m]
(build : Module → List α → BuildM α)
: RecBuild Module α m := fun mod recurse => do
  have : MonadLift BuildM m := ⟨liftM⟩
  have : MonadFunctor BuildM m := ⟨fun f => monadMap (m := BuildM) f⟩
  let contents ← IO.FS.readFile mod.srcFile
  let (imports, _, _) ← Elab.parseImports contents mod.src.file.toString
  -- we construct the import targets even if a rebuild is not required
  -- because other build processes (ex. `.o`) rely on the map being complete
  let importTargets ← imports.filterMapM fun imp => OptionT.run do
    let mod := imp.module
    let pkg ← OptionT.mk <| getPackageForModule? mod
    recurse ⟨pkg, mod⟩
  build mod importTargets

def recBuildModuleOleanAndCTargetWithLocalImports
[Monad m] [MonadLiftT BuildM m] [MonadFunctorT BuildM m] (depTarget : ActiveBuildTarget x)
: RecBuild Module ActiveOleanAndCTarget m :=
  recBuildModuleWithLocalImports fun mod importTargets => do
    let importTarget ← ActiveTarget.collectOpaqueList <| importTargets.map (·.oleanTarget)
    let allDepsTarget := Target.active <| ← depTarget.mixOpaqueAsync importTarget
    moduleOleanAndCTargetOnly mod allDepsTarget |>.activate

def recBuildModuleOleanTargetWithLocalImports
[Monad m] [MonadLiftT BuildM m] [MonadFunctorT BuildM m] (depTarget : ActiveBuildTarget x)
: RecBuild Module ActiveOleanTarget m :=
  recBuildModuleWithLocalImports fun mod importTargets => do
    let importTarget ← ActiveTarget.collectOpaqueList importTargets
    let allDepsTarget ← depTarget.mixOpaqueAsync importTarget
    let task ← liftM <| allDepsTarget.bindOpaqueSync mod.olean.build1
    ActiveTarget.mk mod.olean task

-- ## Definitions

abbrev ModuleBuildM (α) :=
  -- equivalent to `RBTopT (cmp := Name.quickCmp) Name α BuildM`.
  -- phrased this way to use `NameMap`
  EStateT (List Name) (NameMap α) BuildM

abbrev RecModuleBuild (o) :=
  RecBuild Module o (ModuleBuildM o)

abbrev RecModuleTargetBuild (i) :=
  RecModuleBuild (ActiveBuildTarget i)

-- ## Builders

/-- Build a single module using the recursive module build function `build`. -/
def buildModule (mod : Module)
[Inhabited o] (build : RecModuleBuild o) : BuildM o := do
  failOnBuildCycle <| ← RBTopT.run' do
    buildRBTop (cmp := Name.quickCmp) build Module.name mod

/--
Build each module using the recursive module function `build`,
constructing an `Array`  of the results.
-/
def buildModuleArray (mods : Array Module)
[Inhabited o] (build : RecModuleBuild o) : BuildM (Array o) := do
  failOnBuildCycle <| ← RBTopT.run' <| mods.mapM <|
    buildRBTop (cmp := Name.quickCmp) build Module.name

/--
Build each module using the recursive module function `build`,
constructing a module-target `NameMap`  of the results.
-/
def buildModuleMap [Inhabited o]
(infos : Array Module) (build : RecModuleBuild o)
: BuildM (NameMap o) := do
  let (x, objMap) ← RBTopT.run do
    infos.forM fun info => discard <| buildRBTop build Module.name info
  failOnBuildCycle x
  return objMap
