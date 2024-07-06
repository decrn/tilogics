FROM coqorg/coq:8.17
LABEL maintainer="steven.keuchel@gmail.com"

# Install coq libraries
RUN opam install -vyj$(nproc) coq-iris=4.1.0 coq-equations=1.3+8.17 \
&& opam clean -acrs --logs \
&& opam config list && opam list

# Install system packages
RUN sudo apt-get update -yq \
&& DEBIAN_FRONTEND=noninteractive sudo apt-get install -yq --no-install-recommends \
   cabal-install ghc git libghc-optparse-applicative-dev \
&& sudo apt-get clean \
&& sudo rm -fr /var/lib/apt/lists/*

# Clone artifact repository
RUN git clone https://github.com/decrn/tilogics.git
WORKDIR tilogics
