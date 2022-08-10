FROM gitpod/workspace-full

# Install custom tools, runtime, etc.
RUN brew install agda; \
  brew install haskell-language-server; \
  brew uninstall --ignore-dependencies emacs; brew deps emacs | xargs -n 1 brew uninstall --ignore-dependencies; \
  rm -rf /home/linuxbrew/.linuxbrew/etc/unbound; \
  rm -rf /home/linuxbrew/.linuxbrew/etc/gnutls; \
  rm -rf /home/linuxbrew/.linuxbrew/etc/openssl@1.1; \
  rm -rf /home/linuxbrew/.linuxbrew/etc/ca-certificates; \
  rm -rf /home/linuxbrew/.linuxbrew/share/emacs/site-lisp/agda;
RUN sed -i -e 's/gcc-5/gcc-9/g' /home/linuxbrew/.linuxbrew/Cellar/ghc/8.10.7_1/lib/ghc-8.10.7/settings;
RUN cabal update; cabal install --lib ieee754; cabal install --lib network;
