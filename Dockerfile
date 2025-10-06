FROM ubuntu:24.04

# Install dependencies
RUN apt-get update && apt-get install -y \
    wget \
    tar \
    openjdk-21-jdk \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Set JAVA_HOME
ENV JAVA_HOME=/usr/lib/jvm/java-21-openjdk-amd64
ENV PATH="$JAVA_HOME/bin:$PATH"

# Download and install TLAPS 1.6.0-pre
RUN wget https://github.com/tlaplus/tlapm/releases/download/1.6.0-pre/tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz && \
    tar -xzf tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz && \
    mv tlapm /usr/local/tlapm && \
    rm tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz

ENV PATH="/usr/local/tlapm/bin:$PATH"

# Download and install Isabelle 2025
RUN wget https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle2025_linux.tar.gz && \
    tar -xzf Isabelle2025_linux.tar.gz && \
    mv Isabelle2025 /usr/local/Isabelle && \
    rm Isabelle2025_linux.tar.gz

ENV ISABELLE_HOME=/usr/local/Isabelle
ENV PATH="/usr/local/Isabelle/bin:$PATH"

# Set working directory
WORKDIR /workspace

# Copy project files
COPY . /workspace

# Build ArithmeticIsa Isabelle session
RUN cd /workspace/proofs && isabelle build -d . -b -v ArithmeticIsa

# Set environment variables for TLAPS
ENV TLA_PATH="/workspace/tla:/workspace/proofs"

# Default command: run all proofs
CMD ["sh", "-c", "tlapm -C --stretch 6 -I proofs -I tla proofs/QuorumIntersection.tla 2>&1 | tee verification_logs/tlaps_quorum_docker.log && \
     tlapm -C --stretch 6 -I proofs -I tla proofs/CertificateUniqueness.tla 2>&1 | tee verification_logs/tlaps_cert_docker.log && \
     tlapm -C --stretch 6 -I proofs -I tla proofs/FinalizationSafety.tla 2>&1 | tee verification_logs/tlaps_final_docker.log"]
