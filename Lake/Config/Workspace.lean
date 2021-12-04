/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Opaque
import Lake.Config.WorkspaceConfig
import Lake.Config.Package

open System
namespace Lake

/-- A Lake workspace -- the top-level package directory. -/
structure Workspace where
  /-- The path to the workspace's directory. -/
  dir : FilePath
  /-- The workspace's configuration. -/
  config : WorkspaceConfig
  deriving Inhabited, Repr

namespace OpaqueWorkspace

unsafe def unsafeMk (ws : Workspace) : OpaqueWorkspace :=
  unsafeCast ws

@[implementedBy unsafeMk] constant mk (ws : Workspace) : OpaqueWorkspace :=
  OpaqueWorkspacePointed.val

instance : Coe Workspace OpaqueWorkspace := ⟨mk⟩
instance : Inhabited OpaqueWorkspace := ⟨mk Inhabited.default⟩

unsafe def unsafeGet (self : OpaqueWorkspace) : Workspace :=
  unsafeCast self

@[implementedBy unsafeGet] constant get (self : OpaqueWorkspace) : Workspace

instance : Coe OpaqueWorkspace Workspace := ⟨get⟩

@[simp] axiom get_mk {ws : Workspace} : get (mk ws) = ws

end OpaqueWorkspace

namespace Workspace

def ofPackage (pkg : Package) : Workspace :=
  {dir := pkg.dir, config := pkg.config.toWorkspaceConfig}

/-- The workspace's `dir` joined with its `depsDir` configuration. -/
def depsDir (self : Workspace) : FilePath :=
  self.dir / self.config.depsDir
