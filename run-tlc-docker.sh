#!/usr/bin/env bash
set -euo pipefail

IMAGE_NAME=solana-alpenglow-verifier
PLATFORM=${PLATFORM:-linux/amd64}
IMAGE_TAG=${PLATFORM##*/}
MODE=${1:-quick}

echo "========================================="
echo "Solana Alpenglow TLC Docker Verification"
echo "Building $PLATFORM image"
echo "Mode: $MODE"
echo "========================================="
echo ""

if ! command -v docker >/dev/null 2>&1; then
  echo "Docker CLI not found. Please install Docker Desktop or the Docker Engine." >&2
  exit 1
fi

if ! docker info >/dev/null 2>&1; then
  echo "Docker daemon is not reachable. Start Docker Desktop or the daemon before running this script." >&2
  exit 1
fi

mkdir -p verification_logs/tlc_results

echo "Building Docker image (TLC-only, fast build)..."
docker build --platform=$PLATFORM \
  --build-arg TARGETARCH=${PLATFORM##*/} \
  -f Dockerfile.tlc -t ${IMAGE_NAME}:tlc-${IMAGE_TAG} .

echo ""
echo "Docker image built successfully!"
echo ""
echo "Running TLC in Docker container..."
echo ""

docker run --rm --platform=$PLATFORM \
  -e MODE="$MODE" \
  -v "$(pwd)/verification_logs:/workspace/verification_logs" \
  ${IMAGE_NAME}:tlc-${IMAGE_TAG} "$MODE"

echo ""
echo "========================================="
echo "TLC verification complete!"
echo "Results saved to: verification_logs/tlc_results/"
echo "========================================="
