{
  sources ? import ./npins,
  system ? builtins.currentSystem,
  pkgs ? import sources.nixpkgs {
    inherit system;
    config = { };
  },
}:
let
  lib = pkgs.lib;

  # This is a utility not exposed by nixpkgs.leanPackages
  # Generate the overrides from a list of lean packages
  mkOverridesFile =
    allLeanDeps:
    pkgs.writeText "lake-overrides.json" (
      builtins.toJSON {
        schemaVersion = "1.2.0";
        packages = map (dep: {
          type = "path";
          name = dep.passthru.lakePackageName or dep.pname;
          inherited = false;
          dir = "${dep}";
        }) allLeanDeps;
      }
    );

  lean4-src-branch = pkgs.fetchFromGitHub {
    repo = "lean4";
    owner = "xhalo32";
    rev = "de81323214ba25d8080acbe3edd5917f4bd38936";
    hash = "sha256-Kvd/bN7EqrQPy+49d7ULPSR9QtZhbCGh8Ol1+pW3VKM=";
  };

  leanPackagesPatched = pkgs.leanPackages.overrideScope (
    self: super: {
      lean4 = (
        super.lean4.override {
          # HACK inject custom lean4 to leanPackages
          fetchFromGitHub =
            args:
            if args.repo or "" == "lean4" then
              # lean4-src-local
              lean4-src-branch // { tag = args.tag; } # This is used as LEAN_GITHASH which needs to match the version mathlib etc. are built against
            else
              pkgs.fetchFromGitHub args;
        }
      );
    }
  );

  leanclient = pkgs.python3Packages.callPackage  ./leanclient.nix {};

  analysis = pkgs.leanPackages.buildLakePackage {
    pname = "analysis";
    version = "0.1.0";
    src = pkgs.nix-gitignore.gitignoreSource [ ] ./.;
    leanPackageName = "analysis";
    buildTargets = [ "Analysis1Notes" ];
    leanDeps = [ pkgs.leanPackages.mathlib ];
  };

  pythonEnv = 
      pkgs.python3.withPackages (ps: with ps; [leanclient ipython watchdog]);

  tui = pkgs.writeShellScriptBin "tui" ''
    ${lib.getExe pythonEnv} ${./scripts/lean_tui.py} "$@"
  '';
in
{
  inherit leanclient tui;

  shell = pkgs.mkShellNoCC {
    buildInputs = [
      leanPackagesPatched.lean4
      pythonEnv
      tui
    ];
    LAKE_PACKAGES = mkOverridesFile analysis.passthru.allLeanDeps;
  };
}
