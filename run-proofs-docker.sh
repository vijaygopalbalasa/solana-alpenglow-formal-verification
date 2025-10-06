#!/bin/bash
set -e

echo "Building Docker image with TLAPS + Isabelle..."
docker build -t solana-alpenglow-verifier .

echo ""
echo "Running proofs in Docker container..."
echo "This will take several minutes..."
echo ""

# Create logs directory if it doesn't exist
mkdir -p verification_logs

# Run the container
docker run --rm \
  -v "$(pwd)/proofs/.tlacache:/workspace/proofs/.tlacache" \
  -v "$(pwd)/verification_logs:/workspace/verification_logs" \
  solana-alpenglow-verifier

echo ""
echo "Proofs complete! Check:"
echo "  - verification_logs/*.log for proof output"
echo "  - proofs/.tlacache/ for completed proofs"
