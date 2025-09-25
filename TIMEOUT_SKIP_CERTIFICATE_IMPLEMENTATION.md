# Timeout and Skip Certificate Implementation

## Overview

This document describes the implementation of timeout mechanisms and skip certificate logic in the Alpenglow TLA+ specification, completing task 4 of the enhanced verification system.

## Implementation Details

### 1. New State Variables

Added four new state variables to track timeout and skip certificate state:

- `timeouts`: Set of slots that have timed out
- `skip_certs`: Set of skip certificates generated for timed out slots  
- `slot_start_time`: Function mapping slots to their start times
- `current_time`: Current system time for timeout calculations

### 2. New Constants

Added two new constants for timeout configuration:

- `SlotTimeout`: Maximum time allowed for a slot before timeout
- `MaxTime`: Maximum system time to bound model checking

### 3. Timeout Detection Logic

#### Core Functions:

- `SlotHasTimedOut(sl)`: Checks if slot has exceeded timeout duration
- `NoProgressInSlot(sl)`: Checks if slot has insufficient votes for any quorum
- `ShouldTimeoutSlot(sl)`: Combines time and progress conditions for timeout
- `CascadingTimeoutCondition(sl)`: Detects when cascading timeouts should occur

#### Timeout Conditions:

A slot times out when:
1. Current time - slot start time >= SlotTimeout
2. No block in the slot has enough votes to meet even the 60% quorum
3. The slot hasn't already been marked as timed out

### 4. Skip Certificate Generation

#### Skip Certificate Structure:
```tla
[slot |-> sl, type |-> "skip", timestamp |-> current_time]
```

#### Generation Rules:
- Skip certificates can only be generated for slots that have timed out
- Each slot can have at most one skip certificate
- Skip certificates maintain the same uniqueness properties as regular certificates

### 5. Cascading Timeout Handling

#### Cascading Logic:
- If previous slot timed out and current slot should also timeout, trigger cascading
- Limited to maximum 3 consecutive timeouts to prevent infinite loops
- Handles multiple slots timing out simultaneously

#### Bounded Cascading:
- `CountConsecutiveTimeouts(sl)`: Recursively counts consecutive timeouts
- `CascadingTimeoutBounds`: Invariant ensuring cascading is bounded

### 6. Certificate Uniqueness Enhancement

Enhanced certificate uniqueness to include skip certificates:

- `CertificateUnique(sl)`: Now checks both regular and skip certificates
- `GlobalCertificateUniqueness`: Ensures no slot has both types of certificates
- `CertificateAggregationInvariants`: Extended to validate skip certificates

### 7. New Actions

#### Primary Actions:
- `TimeoutSlot(sl)`: Marks a slot as timed out when conditions are met
- `GenerateSkipCertificate(sl)`: Creates skip certificate for timed out slot
- `HandleCascadingTimeout`: Handles multiple consecutive timeouts
- `AdvanceTime`: Models passage of time for timeout calculations

#### Enhanced Actions:
- `FinalizeBlock`: Now accepts skip certificates for finalization
- `HasValidCertificate`: Checks both regular and skip certificates

### 8. Invariants and Properties

#### New Invariants:
- `TimeoutConsistency`: Timed out slots are not finalized
- `SkipCertificateConsistency`: Skip certificates only exist for timed out slots
- `GlobalCertificateUniqueness`: No conflicting certificates per slot
- `CascadingTimeoutBounds`: Cascading timeouts are bounded
- `TimeProgressionConsistency`: Time variables are consistent

#### Liveness Properties:
- Eventually some slot gets finalized or times out
- If slot times out, skip certificate can be generated
- Progress is maintained even under timeout conditions

### 9. Test Configuration

Created `MC_Timeout_Test.cfg` and `MC_Timeout_Test.tla` for testing:

- 4-node configuration with 1 Byzantine node
- SlotTimeout = 5, MaxTime = 20
- Tests timeout detection, skip certificate generation, and cascading scenarios
- Verifies all timeout-related invariants and properties

## Requirements Satisfaction

### Requirement 3.1: Timeout Detection
✅ **WHEN a slot times out THEN the system SHALL generate appropriate skip certificates**
- Implemented `ShouldTimeoutSlot` for timeout detection
- `GenerateSkipCertificate` creates skip certificates for timed out slots

### Requirement 3.2: Slot Progression  
✅ **WHEN timeout conditions are met THEN slot progression SHALL continue using skip certificate logic**
- `TimeoutSkip` advances slots when timeout occurs
- `FinalizeBlock` accepts skip certificates for finalization

### Requirement 3.3: Cascading Timeouts
✅ **WHEN multiple timeout scenarios occur THEN the system SHALL handle cascading timeouts correctly**
- `HandleCascadingTimeout` manages multiple consecutive timeouts
- `CascadingTimeoutBounds` ensures bounded cascading behavior

### Requirement 3.4: Certificate Uniqueness
✅ **WHEN skip certificates are generated THEN they SHALL maintain proper certificate uniqueness properties**
- Enhanced `CertificateUnique` to include skip certificates
- `GlobalCertificateUniqueness` prevents conflicting certificates
- Skip certificates follow same validation rules as regular certificates

## Testing and Verification

The implementation can be verified using the provided test configuration:

```bash
tlc -config MC_Timeout_Test.cfg MC_Timeout_Test.tla
```

Key test scenarios:
1. Normal timeout when no progress is made
2. Skip certificate generation after timeout
3. Cascading timeout handling
4. Certificate uniqueness preservation
5. Time progression and bounds checking

## Integration with Existing System

The timeout and skip certificate logic integrates seamlessly with existing components:

- **Votor**: Voting continues normally, timeout detection based on vote aggregation
- **Rotor**: Block propagation unaffected, timeouts based on finalization progress  
- **Certificates**: Skip certificates follow same validation and uniqueness rules
- **Byzantine Handling**: Timeout detection accounts for Byzantine vote behavior

This implementation provides a robust foundation for modeling realistic consensus behavior under network delays and failures, enabling comprehensive liveness property verification.