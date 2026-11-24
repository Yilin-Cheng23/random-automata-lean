#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ "${1:-}" != --in-lake-env ]]; then
    exec lake env bash ./verify.sh --in-lake-env
fi
dest=$(mktemp -d)
trap 'rm -rf "$dest"' EXIT
export LEAN_PATH="$dest:$LEAN_PATH"
lean --version
for mod in OverlapWords SurvivalEnvelope SurvivalCone PredictiveFolding DualSeparation CenteredRowEdits SignatureSupport MatchingContrast FiniteTemplateProbe AdjacentHistory CommonWordMoments FourSourceCoefficient BlindHistoryFilter InvisiblePorts OriginExperiment SuffixCellContrast WeakPrediction HiddenAbsorber SinglePrefixRelation SignedWalshCollision CriticalWindowCoefficient DeletionRootGap; do
    lean -DwarningAsError=true -o "$dest/$mod.olean" "$mod.lean"
    leanchecker -v --fresh "$mod"
done
