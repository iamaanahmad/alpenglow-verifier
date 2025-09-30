# Stake-Weighted Relay Sampling Implementation Summary

## Task 3: Implement stake-weighted relay sampling for Rotor

### Implementation Details

#### 1. New Constants Added
- `ErasureCodingFactor`: Configurable redundancy factor for erasure coding
- `NetworkDelay`: Network delay parameter for topology modeling

#### 2. New Variables Added
- `relay_graph`: Tracks relay relationships between nodes
- `network_topology`: Models network delay between node pairs

#### 3. Core Functions Implemented

**Stake-Weighted Sampling:**
- `CanRelay(n, sender, b)`: Checks if a node can relay a block
- `RelayProbability(n)`: Calculates relay probability based on stake weight
- `EligibleRelays(sender, b)`: Gets eligible relay nodes for a block
- `StakeWeightedSample(sender, b, target_count)`: Deterministic sampling based on stake weights

**Erasure Coding:**
- `ErasureCodingRedundancy`: Uses configurable redundancy factor
- `MinRelaysForErasureCoding`: Calculates minimum relays needed
- `ErasureCodingRedundancyMaintained`: Invariant to ensure redundancy is maintained

**Network Topology:**
- `GetNetworkDelay(n1, n2)`: Gets network delay between nodes
- `NetworkPropagationEfficiency(sender, receivers)`: Models topology effects
- `IsEfficientRelay(sender, receiver, b)`: Checks single-hop efficiency

#### 4. Enhanced Actions

**StakeWeightedRelayBlock(sender, b, sl):**
- Replaces simple relay with probabilistic selection
- Uses stake-weighted sampling to select relay targets
- Implements erasure coding with configurable redundancy
- Updates relay graph to track relationships

**RelayBlock(sender, receiver, b, sl):** (Updated)
- Enhanced with efficiency checks
- Respects network topology constraints
- Updates relay graph

#### 5. New Invariants Added
- `RelayGraphConsistency`: Ensures relay graph matches block distribution
- `StakeWeightedSamplingFairness`: Verifies higher stake nodes are preferred
- `ErasureCodingRedundancyMaintained`: Ensures redundancy requirements
- `NetworkTopologyRespected`: Verifies network delay constraints

#### 6. Configuration Updates
- Updated `MC_Certificate_Test.cfg` and `MC_Byzantine_Test.cfg`
- Added new constants and invariants to test configurations

### Requirements Satisfied

✅ **Requirement 2.1**: Probabilistic relay selection based on stake weights
- Implemented `StakeWeightedSample` function
- Higher stake nodes have higher probability of being selected

✅ **Requirement 2.2**: Erasure coding logic with configurable redundancy
- Added `ErasureCodingFactor` constant
- Implemented `MinRelaysForErasureCoding` calculation
- Ensured redundancy through invariants

✅ **Requirement 2.3**: Network topology effects on block propagation
- Added `network_topology` variable
- Implemented `NetworkPropagationEfficiency` function
- Models realistic network delays

✅ **Requirement 2.4**: Single-hop block distribution efficiency
- Implemented `IsEfficientRelay` function
- Added `SingleHopDistributionEfficient` verification
- Ensured efficient propagation through stake-weighted selection

### Key Features

1. **Probabilistic Selection**: Nodes with higher stake have higher probability of being selected as relays
2. **Erasure Coding**: Configurable redundancy factor ensures fault tolerance
3. **Network Modeling**: Realistic network delays and topology effects
4. **Efficiency Guarantees**: Single-hop distribution with optimal relay selection
5. **Byzantine Resilience**: Only honest nodes participate in relay (Byzantine nodes excluded from relay sampling)

The implementation successfully transforms the simple relay mechanism into a sophisticated stake-weighted system that models the Rotor protocol's erasure-coded block propagation with proper network topology considerations.