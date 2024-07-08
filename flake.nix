{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = inputs:
    inputs.flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import inputs.nixpkgs {inherit system;};
        # Function to override versions of coq packages. This function takes two arguments:
        # - coqPackages: The set of all Coq packages.
        # - versions: An attribute set of packages with their versions we want to override.
        patchCoqPackages = coqPackages: versions:
          coqPackages.overrideScope (
            _self: super:
              pkgs.lib.foldlAttrs
              # foldAttrs is used to iterate over the versions set and apply a function
              # to each attribute. This function takes three arguments: the accumulator set,
              # the attribute name (package name), and the attribute value (version).
              (acc: pkg: version:
                # This function returns a new set with the current attribute added to the
                # accumulator set. The attribute name is the package name, and the value
                # is the overridden package.
                  acc // {${pkg} = super.${pkg}.override {inherit version;};})
              # The initial value of the accumulator set.
              {}
              # The attribute set to iterate over.
              versions
          );

        iris41 = {
          iris = "4.1.0";
          stdpp = "1.9.0";
        };

        iris42 = {
          iris = "4.2.0";
          stdpp = "1.10.0";
        };

        mkShell = coqPackages: irisVersions: 
          let cp = patchCoqPackages coqPackages irisVersions; in
          pkgs.mkShell {buildInputs = [cp.coq cp.equations cp.stdpp cp.iris];};

      in {
        devShells = rec {
          default = coq817_iris41;
          coq816_iris41 = mkShell pkgs.coqPackages_8_16 iris41;
          coq817_iris41 = mkShell pkgs.coqPackages_8_17 iris41;
          coq818_iris41 = mkShell pkgs.coqPackages_8_18 iris41;
          coq818_iris42 = mkShell pkgs.coqPackages_8_18 iris42;
          coq819_iris42 = mkShell pkgs.coqPackages_8_19 iris42;
        };
      }
    );
}
