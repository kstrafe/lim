{
  nixConfig.bash-prompt-suffix = "\[nix\] ";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
    flake-utils.url = "github:numtide/flake-utils";
  };


  outputs = inputs:
    inputs.flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import inputs.nixpkgs {
        inherit system;
        overlays = [
          inputs.rust-overlay.overlays.default
        ];
      };

      rust-collection = pkgs.rust-bin.nightly.latest.default.override {
        extensions = [ "miri-preview" "rust-src" ];
      };

      packages = with pkgs; [
        alsa-lib
        libpulseaudio
        lm_sensors

        cmake
        fontconfig.dev
        just
        libGL
        libxkbcommon
        libxkbcommon
        pkg-config
        openssl.dev
        python312Packages.cogapp.out
        rust-collection
        vulkan-loader
        vulkan-validation-layers
        wayland
        libx11
        libxcursor
        libxi
        libxrandr
        valgrind
      ] ++ lib.optionals stdenv.isLinux [ strace qemu-user ];
    in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = packages;

          # glibc warns that _FORTIFY_SOURCE needs an optimized build,
          # every time a debug build compiles the vendored C++. The
          # define comes from this shell's own hardening, and the
          # compiler wrapper appends it after anything a build script
          # passes, so it can only be turned off here.
          hardeningDisable = [ "fortify" ];

          shellHook = ''
            if [ -z "$LD_LIBRARY_PATH" ]; then
              export LD_LIBRARY_PATH=${pkgs.lib.makeLibraryPath packages}
            else
              export LD_LIBRARY_PATH=''$LD_LIBRARY_PATH:${pkgs.lib.makeLibraryPath packages}
            fi
            export SHADERC_LIB_DIR="${pkgs.lib.makeLibraryPath [pkgs.shaderc.lib]}"

            export VK_LAYER_PATH="${pkgs.vulkan-validation-layers}/share/vulkan/explicit_layer.d";
          '';
        };

        devShells.validation = pkgs.mkShell {
          buildInputs = packages;

          # As the default shell above.
          hardeningDisable = [ "fortify" ];

          shellHook = ''
            if [ -z "$LD_LIBRARY_PATH" ]; then
              export LD_LIBRARY_PATH=${pkgs.lib.makeLibraryPath packages}
            else
              export LD_LIBRARY_PATH=''$LD_LIBRARY_PATH:${pkgs.lib.makeLibraryPath packages}
            fi

            export SHADERC_LIB_DIR="${pkgs.lib.makeLibraryPath [pkgs.shaderc.lib]}"

            export VK_INSTANCE_LAYERS=VK_LAYER_KHRONOS_validation
            export VK_LOADER_LAYERS_ENABLE=VK_LAYER_KHRONOS_validation

            export VK_LAYER_PATH="${pkgs.vulkan-validation-layers}/share/vulkan/explicit_layer.d";
            export VK_LOADER_DEBUG= # Can be error,warn,layer,all
            # export INCDIRS_VK_MEM_RS="${pkgs.vulkan-headers.out}/include"

            function recheck {
              fd | entr -c bash -c 'first-page cargo check --color=always'
            }
          '';
        };
      }
    );
}
