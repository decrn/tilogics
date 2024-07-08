FROM debian:bookworm-slim
LABEL maintainer="steven.keuchel@gmail.com"

# Install system packages
RUN apt-get update -yq \
&& DEBIAN_FRONTEND=noninteractive apt-get install -yq --no-install-recommends \
   autoconf automake ca-certificates cabal-install git hyperfine \
   libghc-optparse-applicative-dev libgmp-dev m4 ocaml-nox opam pkg-config \
   python3 rsync sudo time zlib1g-dev \
&& apt-get clean \
&& rm -fr /var/lib/apt/lists/*

# Add coq user and drop root
RUN useradd -lmU -s /bin/bash -G sudo -p '' coq
WORKDIR /home/coq
USER coq

# Install common packages
RUN set -x \
&& opam init -j$(nproc) --compiler ocaml-system --auto-setup --yes --disable-completion --disable-sandboxing \
&& opam repo add --all-switches --set-default coq-released https://coq.inria.fr/opam/released \
&& opam install -vyj$(nproc) dune num ocamlfind zarith conf-findutils conf-gmp opam-depext \
&& opam clean -acrs --logs \
&& opam config list && opam list

ENTRYPOINT ["opam", "exec", "--"]
CMD ["/bin/bash", "--login"]

# Install coq libraries
RUN opam install -vyj$(nproc) coq-iris=4.1.0 coq-equations=1.3+8.17 \
&& opam clean -acrs --logs \
&& opam config list && opam list

# Clone artifact repository
RUN git clone --depth=1 https://github.com/decrn/tilogics.git
WORKDIR tilogics


