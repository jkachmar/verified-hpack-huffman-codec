{
  description = "verified-hpack-huffman — an F*/Low* HPACK Huffman codec proven correct (RFC 7541 §5.2 & App. B) and lowered to C via KaRaMeL";

  # nixpkgs + karamel are pinned to the exact revisions the proof was checked
  # against in the monorepo this was extracted from, so `pkgs.fstar` is the same
  # F* (2026.03.24). Verification is sensitive to the F* version; do not float
  # these without re-running `make verify`.
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/8c3cede7ddc26bd659d2d383b5610efbd2c7a16e";
    flake-utils.url = "github:numtide/flake-utils";
    karamel-src = {
      flake = false;
      url = "github:fstarlang/karamel/11bb8e1ac2f720fb7144b9b768c7251526caa149";
    };
  };

  outputs = { self, nixpkgs, flake-utils, karamel-src }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        lib = pkgs.lib;

        # KaRaMeL (F*->C), built from the pinned upstream source. Mirrors the
        # construction in the source monorepo, incl. the macOS `gtime` wrapper.
        karamel =
          (pkgs.callPackage "${karamel-src}/.nix/karamel.nix" { version = "dirty"; }).overrideAttrs (old: {
            buildInputs = [ pkgs.git ] ++ lib.optionals pkgs.stdenv.hostPlatform.isDarwin [
              (pkgs.stdenv.mkDerivation {
                name = "gtime";
                nativeBuildInputs = [ pkgs.makeWrapper ];
                buildCommand = ''
                  mkdir -p $out/bin
                  makeWrapper ${pkgs.time}/bin/time $out/bin/gtime
                '';
              })
            ];
          });
      in {
        devShells.default = pkgs.mkShell {
          # Proof toolchain (`make verify` / `make generate`) + the C test/bench
          # harness toolchain (just a C compiler; the differential test links a
          # vendored reference decoder, not an external library).
          buildInputs = [
            karamel
            pkgs.fstar
            pkgs.gnumake
            pkgs.python3
            pkgs.clang
          ];
          shellHook = ''
            export KRML_HOME="${karamel.home}"
            echo "verified-hpack-huffman dev shell"
            echo "  fstar.exe: $(command -v fstar.exe)"
            echo "  KRML_HOME=$KRML_HOME"
          '';
        };
      });
}
