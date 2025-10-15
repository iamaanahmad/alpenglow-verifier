# 📹 DETAILED VISUAL RECORDING GUIDE
## What to Show on Screen During Each Script Line

**Setup**: Read script on phone → Record screen on laptop → Your voice explains what's on screen

---

## 🎬 PART 1: Introduction (0:00 - 1:00)

### Scene 1A: Open VS Code with README.md
**📱 PHONE SCRIPT SAYS:**
> "Hello everyone! I'm showing you the formal verification of Alpenglow..."

**💻 LAPTOP SCREEN SHOWS:**
1. Open VS Code
2. Make sure README.md is open and visible
3. Scroll to TOP of README.md
4. **IMPORTANT**: Show the badges section clearly:
   ```
   ✅ Tests: 7/7 Passing (100%)
   ✅ Properties: 12 Verified
   ```

**🎯 TIMING**: Keep README.md on screen for full 15-20 seconds while you say the introduction

**🎥 CAMERA ACTION**: 
- Slowly scroll from top to show the badges
- Pause on the badges (let viewers read)
- Then scroll down slowly to show table of contents

---

### Scene 1B: Show Test Results Section
**📱 PHONE SCRIPT SAYS:**
> "See these green badges here? All our 7 tests are passing..."

**💻 LAPTOP SCREEN SHOWS:**
- Still in README.md
- Scroll down to "Test Results" section (should show the 7 test names)
- Keep scrolling slowly so viewers can see:
  - MC_4Nodes_Working ✅
  - MC_7Nodes_Working ✅
  - MC_10Nodes_Working ✅
  - MC_4Nodes_Byzantine ✅
  - MC_4Nodes_Liveness ✅
  - MC_4Nodes_Partition ✅
  - MC_4Nodes_Timing ✅

**🎯 TIMING**: 15-20 seconds while explaining about 12 properties

**💡 PRO TIP**: Move your mouse cursor to point at each test name as you mention "7 tests"

---

## 🎬 PART 2: Running Tests (1:00 - 3:00)

### Scene 2A: Open PowerShell
**📱 PHONE SCRIPT SAYS:**
> "Now I will run all our tests live..."

**💻 LAPTOP SCREEN SHOWS:**
1. Press Win+X and click "Windows PowerShell"
2. OR click on Terminal at bottom of VS Code
3. Make sure you're in the correct folder:
   ```powershell
   cd C:\Projects\alpenglow-verifier
   ```
4. Type this command SLOWLY (so viewers can see what you're typing):
   ```powershell
   .\run_complete_verification.ps1 -Workers 4
   ```

**🎯 TIMING**: Take 10 seconds to type the command slowly

**💡 PRO TIP**: 
- Type slowly and clearly
- Pause 2 seconds after typing before pressing Enter
- This lets viewers see the full command

---

### Scene 2B: Tests Running
**📱 PHONE SCRIPT SAYS:**
> "See, it's running now. This script runs 7 different tests..."

**💻 LAPTOP SCREEN SHOWS:**
- Terminal output showing tests executing
- You'll see text like:
  ```
  Test: MC_4Nodes_Working
  Description: Safety verification (4 nodes)
  Status: PASS
  ```

**🎯 TIMING**: Keep terminal visible for full 1-2 minutes

**🎥 CAMERA ACTION**:
- DON'T touch anything - just let it run
- As each test completes, your voice explains which test it is
- When you say "First test - MC_4Nodes_Working", that test should be on screen
- When you say "Fourth test - MC_4Nodes_Byzantine", scroll up if needed to show that test

**💡 PRO TIP**: 
- If tests run too fast, you can PAUSE recording after each test finishes
- Take a screenshot of that test result
- Then continue recording
- This way you can talk about each test result calmly

---

### Scene 2C: All Tests Complete
**📱 PHONE SCRIPT SAYS:**
> "Perfect! See? All 7 tests PASSED!"

**💻 LAPTOP SCREEN SHOWS:**
- Scroll to bottom of terminal output
- Show the summary section:
  ```
  Results:
    Tests Passed: 7 / 7
    Tests Failed: 0 / 7
    Success Rate: 100%
  ```

**🎯 TIMING**: Hold this screen for 5-10 seconds

**🎥 CAMERA ACTION**: 
- Zoom in a bit if possible (Ctrl + plus key in terminal)
- Make sure the "100%" is clearly visible

---

## 🎬 PART 3: Showing Specification (3:00 - 5:00)

### Scene 3A: Open Alpenglow.tla
**📱 PHONE SCRIPT SAYS:**
> "Now let me show you the actual specification..."

**💻 LAPTOP SCREEN SHOWS:**
1. Click on Alpenglow.tla tab in VS Code (or open from file explorer)
2. Scroll to TOP of file
3. Show the header:
   ```tla
   ---------------- MODULE Alpenglow ----------------
   EXTENDS Naturals, FiniteSets, Sequences, TLC
   ```
4. Press Ctrl+G and type "2249" to show total lines
5. Bottom right corner will show "Line 1 of 2249"

**🎯 TIMING**: 10 seconds to open and show file size

**💡 PRO TIP**: 
- Zoom in: Ctrl + plus several times (make text BIG and readable)
- Font should be large enough that phone camera can see clearly

---

### Scene 3B: Scroll Through Code
**📱 PHONE SCRIPT SAYS:**
> "See here? We have modelled everything - Votor's voting system..."

**💻 LAPTOP SCREEN SHOWS:**
- Slowly scroll through Alpenglow.tla
- Don't scroll too fast! 
- Viewers should see different sections passing by:
  - Variable declarations (lines 15-50)
  - Helper functions (lines 50-200)
  - Votor logic (lines 900-1100)
  - Byzantine behaviors (lines 1200-1400)

**🎯 TIMING**: 20-30 seconds of slow scrolling

**🎥 CAMERA ACTION**:
- Scroll SLOWLY - about 1 page every 5 seconds
- Don't read the code - just show it passing by
- This shows the "volume" of work

---

### Scene 3C: Show NoConflictingBlocksFinalized
**📱 PHONE SCRIPT SAYS:**
> "Now let me show you the most important property..."

**💻 LAPTOP SCREEN SHOWS:**
1. Press Ctrl+F (Find)
2. Type: `NoConflictingBlocksFinalized`
3. Press Enter - it will jump to line ~240
4. Show the property definition:
   ```tla
   NoConflictingBlocksFinalized ==
       \A sl1, sl2 \in DOMAIN finalized :
           (sl1 = sl2) => (finalized[sl1] = finalized[sl2])
   ```

**🎯 TIMING**: Hold this on screen for 15-20 seconds

**🎥 CAMERA ACTION**:
- Use mouse cursor to point at the property name
- Then point at the formula line by line as you explain:
  - "it checks all finalized blocks" → point at `\A sl1, sl2`
  - "if two slots are same number" → point at `(sl1 = sl2)`
  - "then blocks must be same" → point at `finalized[sl1] = finalized[sl2]`

---

### Scene 3D: Show CertificateUniqueness
**📱 PHONE SCRIPT SAYS:**
> "Second important property - CertificateUniqueness..."

**💻 LAPTOP SCREEN SHOWS:**
1. Press Ctrl+F again
2. Type: `CertificateUniqueness`
3. Jump to that property (line ~260)
4. Show the definition:
   ```tla
   CertificateUniqueness ==
       \A c1, c2 \in certs :
           (c1.slot = c2.slot) => (c1 = c2)
   ```

**🎯 TIMING**: 15 seconds

**🎥 CAMERA ACTION**: Similar to previous - use cursor to point

---

## 🎬 PART 4: Byzantine Testing (5:00 - 7:00)

### Scene 4A: Open MC_4Nodes_Byzantine.cfg
**📱 PHONE SCRIPT SAYS:**
> "Now let me show you the Byzantine testing..."

**💻 LAPTOP SCREEN SHOWS:**
1. Click on MC_4Nodes_Byzantine.cfg tab (or open file)
2. Show the top part of config:
   ```
   CONSTANTS
       Nodes = {n1, n2, n3, n4}
       ByzantineNodes = {n4}
       ByzantineStakeRatio = 25
   ```

**🎯 TIMING**: 10 seconds

**🎥 CAMERA ACTION**:
- Use cursor to point at `ByzantineNodes = {n4}` when you say "node n4 is Byzantine"
- Point at `ByzantineStakeRatio = 25` when you say "25% stake"

---

### Scene 4B: Explain Byzantine Attacks
**📱 PHONE SCRIPT SAYS:**
> "In our TLA+ model, this Byzantine node can do three types of attacks..."

**💻 LAPTOP SCREEN SHOWS:**
- Still showing MC_4Nodes_Byzantine.cfg
- OR switch to Alpenglow.tla and search for `ByzantineBehaviorTypes`
- Show the line:
  ```tla
  ByzantineBehaviorTypes == {"double_vote", "withhold_vote", "vote_invalid", "normal"}
  ```

**🎯 TIMING**: 15-20 seconds while you list the 3 attacks

**💡 PRO TIP**: You can point at each attack type with cursor as you mention it

---

### Scene 4C: Show Byzantine Test Results
**📱 PHONE SCRIPT SAYS:**
> "But see the results? Even with these attacks, all tests passed!"

**💻 LAPTOP SCREEN SHOWS:**
1. Go back to terminal/PowerShell where tests ran
2. Scroll to find MC_4Nodes_Byzantine results
3. Show the line:
   ```
   Test: MC_4Nodes_Byzantine
   Status: PASS
   ```

**🎯 TIMING**: 10 seconds

**🎥 CAMERA ACTION**: Use cursor to circle around "PASS" status

---

### Scene 4D: Open MC_4Nodes_Partition.cfg
**📱 PHONE SCRIPT SAYS:**
> "Now something unique - network partition testing..."

**💻 LAPTOP SCREEN SHOWS:**
1. Open MC_4Nodes_Partition.cfg file
2. Show the constants section
3. Point out any partition-related settings

**🎯 TIMING**: 15-20 seconds

**💡 PRO TIP**: If config looks similar to others, just show the filename at top clearly

---

## 🎬 PART 5: Timing & Liveness (7:00 - 8:30)

### Scene 5A: Open MC_4Nodes_Timing.cfg
**📱 PHONE SCRIPT SAYS:**
> "Now let me show you the timing verification..."

**💻 LAPTOP SCREEN SHOWS:**
1. Open MC_4Nodes_Timing.cfg
2. Scroll to show:
   ```
   Delta80 = 1
   Delta60 = 2
   ```

**🎯 TIMING**: 10 seconds

**🎥 CAMERA ACTION**:
- Point at Delta80 = 1 and say "fast path 1 round"
- Point at Delta60 = 2 and say "slow path 2 rounds"

---

### Scene 5B: Open MC_4Nodes_Liveness.cfg
**📱 PHONE SCRIPT SAYS:**
> "For liveness testing, we check two critical things..."

**💻 LAPTOP SCREEN SHOWS:**
1. Open MC_4Nodes_Liveness.cfg
2. Scroll down to PROPERTIES section
3. Show:
   ```
   PROPERTIES
       ProgressWithHonestSupermajority
       FastPathCompletion
   ```

**🎯 TIMING**: 15-20 seconds

**🎥 CAMERA ACTION**: Point at each property name as you mention it

---

## 🎬 PART 6: What Makes Special (8:30 - 9:30)

### Scene 6A: Keep Terminal or Show README
**📱 PHONE SCRIPT SAYS:**
> "Now let me tell you what makes this verification comprehensive..."

**💻 LAPTOP SCREEN SHOWS:**
- OPTION 1: Keep PowerShell terminal visible (showing 7/7 passed)
- OPTION 2: Switch back to README.md tab
- **DON'T show the scoring section (95/100) from BOUNTY_COMPLIANCE_FINAL.md**

**🎯 TIMING**: 10 seconds intro

**💡 PRO TIP**: 
- Focus on FACTS not self-scoring
- Let the results speak for themselves
- Judges will score based on what they see

---

### Scene 6B: Explain What Was Verified
**📱 PHONE SCRIPT SAYS:**
> "This project verifies 12 different properties..."

**💻 LAPTOP SCREEN SHOWS:**
- Stay in README.md OR terminal
- If you want, you can BRIEFLY open BOUNTY_COMPLIANCE_FINAL.md
- **IMPORTANT**: If opening it, scroll PAST the scoring section (lines 1-50)
- Go to statistics/comparison section (around lines 150-200)
- Show bullet points of what was tested, NOT the "95/100" score

**🎯 TIMING**: 20-30 seconds

**🎥 CAMERA ACTION**:
- If in README: Point at the features list
- If in BOUNTY_COMPLIANCE: Scroll quickly past "Final Score" section
- Focus on "What was verified" not "How many points"

---

### Scene 6C: Show Comprehensive Features
**📱 PHONE SCRIPT SAYS:**
> "We have 7 complete test configurations..."

**💻 LAPTOP SCREEN SHOWS:**
- Best option: Stay in README.md showing features
- Can show BOUNTY_COMPLIANCE statistics (but NOT scoring)
- List of tests, properties, configurations

**🎯 TIMING**: 20 seconds

**💡 PRO TIP**: 
- Emphasize "12 properties", "7 tests", "100% passing"
- These are FACTS judges can verify
- More convincing than saying "I give myself 95/100"

---

## 🎬 PART 7: Conclusion (9:30 - 10:00)

### Scene 7A: Terminal Summary
**📱 PHONE SCRIPT SAYS:**
> "So let me summarize everything..."

**💻 LAPTOP SCREEN SHOWS:**
- Go back to PowerShell/Terminal
- Scroll to show the final summary:
  ```
  Tests Passed: 7 / 7
  Success Rate: 100%
  ```

**🎯 TIMING**: 15 seconds

**🎥 CAMERA ACTION**: Keep this on screen while you list all 5 summary points

---

### Scene 7B: README Top (Final)
**📱 PHONE SCRIPT SAYS:**
> "This project is completely open source..."

**💻 LAPTOP SCREEN SHOWS:**
1. Go back to README.md
2. Scroll to TOP to show badges again
3. Show the GitHub repository link

**🎯 TIMING**: 10 seconds

---

### Scene 7C: GitHub Repository (Optional)
**📱 PHONE SCRIPT SAYS:**
> "The complete project is at github.com/iamaanahmad/alpenglow-verifier..."

**💻 LAPTOP SCREEN SHOWS:**
- OPTIONAL: Open browser
- Go to your GitHub repository page
- Show the repository with green checkmarks, file list, etc.

**🎯 TIMING**: 5-10 seconds

**💡 PRO TIP**: If you want to skip browser, just show the link in README.md

---

### Scene 7D: End Screen
**📱 PHONE SCRIPT SAYS:**
> "Thank you so much for watching!"

**💻 LAPTOP SCREEN SHOWS:**
- Can show README.md with badges
- OR create a simple end screen in PowerPoint:
  ```
  Alpenglow TLA+ Verification
  100% Test Success Rate
  7 Configurations | 12 Properties | Zero Errors
  github.com/iamaanahmad/alpenglow-verifier
  ```

**🎯 TIMING**: 5 seconds, then fade out

---

## 📋 COMPLETE FILE CHECKLIST

Before you start recording, make sure these files are open in VS Code tabs:

✅ **Tab 1**: README.md (for intro and conclusion)
✅ **Tab 2**: Alpenglow.tla (for showing specification)
✅ **Tab 3**: MC_4Nodes_Byzantine.cfg (for Byzantine testing)
✅ **Tab 4**: MC_4Nodes_Liveness.cfg (for liveness properties)
✅ **Tab 5**: MC_4Nodes_Timing.cfg (for timing bounds)
✅ **Tab 6**: MC_4Nodes_Partition.cfg (for partition testing)
✅ **Tab 7**: BOUNTY_COMPLIANCE_FINAL.md (for comparison)
✅ **Tab 8**: PowerShell Terminal at bottom (for running tests)

**File Status Check:**
- ✅ All 7 MC_*.cfg files exist
- ✅ README.md exists
- ✅ Alpenglow.tla exists
- ✅ BOUNTY_COMPLIANCE_FINAL.md exists
- ⚠️ DAY_3_COMPLETE_REPORT.md mentioned in script → Use BOUNTY_COMPLIANCE_FINAL.md instead

---

## 🎥 RECORDING WORKFLOW

### Step-by-Step Process:

**1. PREPARATION (10 minutes)**
- Open all 8 files/tabs in VS Code
- Zoom in text: Ctrl + + + + + (press 5 times)
- Check font is BIG and readable
- Open PowerShell at bottom
- Make sure you're in correct folder
- Close all other apps (WhatsApp, email, etc.)
- Turn on Focus Assist (Windows notifications OFF)
- Open script on phone
- Keep phone on left side of laptop
- Position phone so you can glance at script while looking at laptop screen

**2. TEST RECORDING (5 minutes)**
- Record 30 seconds test
- Say: "Testing, testing, one two three, this is test recording"
- Stop recording
- Play it back
- Check: Can you hear your voice clearly? Is screen recording working?
- If yes, proceed. If no, fix audio/screen settings.

**3. RECORD PART 1 (3-4 attempts)**
- Read Part 1 from phone
- Record Part 1 on laptop (show README.md)
- If mistake: STOP, delete, try again
- Record until you get one good take
- Save recording as "Part1.mp4"

**4. RECORD PART 2 (3-4 attempts)**
- Read Part 2 from phone
- Record Part 2 (show terminal running tests)
- **TIP**: You can PAUSE recording between tests
- Save as "Part2.mp4"

**5. REPEAT FOR PARTS 3-7**
- Same process
- One part at a time
- Don't rush
- If tired, take 5-minute break

**6. EDIT ALL PARTS TOGETHER (20 minutes)**
- Open Windows Video Editor
- Drag Part1.mp4, Part2.mp4, ... Part7.mp4 into timeline
- Trim any extra pauses at start/end of each part
- Add title card at beginning: "Alpenglow TLA+ Verification"
- Add end screen at end (text with GitHub link)
- Export as "Alpenglow_Verification_Final.mp4"

---

## 💡 IMPORTANT TIPS

### Voice Recording:
- Speak at **80% of normal speed** (a bit slower than usual)
- Pause between sentences (makes editing easier)
- If you stumble on a word, just stop, pause 2 seconds, and say that sentence again
- Don't worry about accent - technical content matters, not accent

### Screen Recording:
- **BIG TEXT** - Zoom in everywhere (VS Code, Terminal, Browser)
- Scroll SLOWLY - Give viewers time to see
- Use mouse cursor to POINT at important things
- Don't type fast - type slowly so viewers can follow

### Common Mistakes to Avoid:
❌ Scrolling too fast (viewers can't see anything)
❌ Text too small (viewers can't read)
❌ Talking too fast (viewers can't understand)
❌ Not pausing between sections (video feels rushed)
❌ Background noise (close windows, turn off fan)

### What to Do If:
- **You make a mistake**: STOP recording, delete that file, record that part again. No problem!
- **Phone script is hard to read**: Increase phone brightness to 100%, or write key points on paper
- **You forget what to say**: PAUSE recording, read script again, RESUME recording. Pause can be edited out.
- **Test takes too long to run**: PAUSE recording after starting test, come back when it finishes, RESUME recording
- **You get nervous**: Remember - this is just showing YOUR excellent work that already exists! You're not creating something new, just showing it.

---

## ⏱️ REALISTIC TIMELINE

- **Preparation**: 15 minutes
- **Recording Part 1**: 15 minutes (3-4 takes)
- **Recording Part 2**: 20 minutes (running tests takes time)
- **Recording Part 3**: 15 minutes
- **Recording Part 4**: 15 minutes
- **Recording Part 5**: 15 minutes
- **Recording Part 6**: 10 minutes
- **Recording Part 7**: 10 minutes
- **Break between parts**: 20 minutes total
- **Editing**: 25 minutes
- **Upload & update README**: 15 minutes

**TOTAL: 2.5 to 3 hours**

Take your time. Quality > Speed!

---

## 🎯 SUCCESS CHECKLIST

Before you upload, watch your final video and check:

- [ ] Audio is clear (can hear your voice)
- [ ] Screen is visible (text is big enough)
- [ ] All 7 test configurations are mentioned
- [ ] You show the tests actually passing
- [ ] You show the TLA+ code
- [ ] You explain Byzantine testing
- [ ] You show the comparison (what makes it special)
- [ ] Video is 9-11 minutes (close to 10)
- [ ] You sound confident and natural
- [ ] Endscreen shows GitHub link

If all checkboxes are ✅, you're ready to upload!

---

## 🚀 FINAL PEP TALK

**You:** Have excellent project (7/7 tests, 12 properties, 100% success)

**Goal:** Make 10-minute video showing your excellent work

**Pressure:** ZERO! The work is done. You're just showing it.

**Result:** +5 points → 100/100 Perfect Score → High chance of winning! 🏆

**Mindset:** You're a teacher showing students your work. Be proud! Be confident! You did something impressive!

---

**Now go make that video and WIN THIS BOUNTY! 💪🎬🏆**
