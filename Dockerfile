FROM ubuntu:24.04

# Install build/runtime dependencies
RUN apt-get update && apt-get install -y \
    build-essential \
    m4 \
    libgmp-dev \
    pkg-config \
    opam \
    git \
    wget \
    curl \
    unzip \
    openjdk-21-jdk \
    && rm -rf /var/lib/apt/lists/*

ENV JAVA_HOME=/usr/lib/jvm/java-21-openjdk-amd64
ENV PATH="$JAVA_HOME/bin:$PATH"

# Bootstrap OCaml environment for TLAPS build
RUN opam init -y --disable-sandboxing && \
    opam switch create tlapm 4.14.1 && \
    eval "$(opam env --switch=tlapm)" && \
    opam install -y dune menhir zarith ppx_deriving batteries stdcompat ocamlfind

# Build TLAPS 1.6.0-pre from source (with Isabelle bundle)
RUN git clone https://github.com/tlaplus/tlapm.git /tmp/tlapm && \
    cd /tmp/tlapm && \
    git checkout 386cb32 && \
    mkdir -p _build_cache && \
    cd _build_cache && \
    wget https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_linux.tar.gz && \
    echo "3d1d66de371823fe31aa8ae66638f73575bac244f00b31aee1dcb62f38147c56  Isabelle2025_linux.tar.gz" | sha256sum -c - && \
    cd .. && \
    eval "$(opam env --switch=tlapm)" && \
    make && \
    make install && \
    rm -rf /tmp/tlapm

ENV TLAPS_HOME=/usr/local/lib/tlapm
ENV PATH="/usr/local/bin:$TLAPS_HOME/bin:$PATH"
ENV ISABELLE_HOME=$TLAPS_HOME/Isabelle

# Workdir
WORKDIR /workspace
COPY . /workspace

# Build Isabelle session and TLAPS config
RUN isabelle build -d proofs -b ArithmeticIsa && \
    cat > proofs/tlaps-docker.cfg <<'CFG'
[prover]
 timeout = 60

[isabelle]
 enabled = true
 image = ArithmeticIsa
CFG

# Proof runner
RUN echo '#!/bin/bash\nset -e\n\nexport PATH="$TLAPS_HOME/bin:/usr/local/bin:$PATH"\nexport TLA_PATH="/workspace/tla:/workspace/proofs"\n\nmkdir -p /workspace/verification_logs\n\nfor mod in QuorumIntersection CertificateUniqueness FinalizationSafety; do\n  echo "===== $mod ====="\n  tlapm -C /workspace/proofs/tlaps-docker.cfg \\n        "/workspace/proofs/${mod}.tla" 2>&1 | tee \
        "/workspace/verification_logs/tlaps_${mod,,}_docker.log"\ndone\n' > /workspace/run-verification.sh && chmod +x /workspace/run-verification.sh

CMD ["/workspace/run-verification.sh"]
