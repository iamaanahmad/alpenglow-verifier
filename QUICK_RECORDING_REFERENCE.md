# 📹 QUICK REFERENCE: Video Recording Setup

## ✅ FILES VERIFICATION

All mentioned files in VIDEO_SCRIPT.md are available:

### Core Files (VERIFIED ✅):
- ✅ **README.md** - For introduction and conclusion
- ✅ **Alpenglow.tla** - Main specification (~2,249 lines)
- ✅ **Properties.tla** - Property definitions
- ✅ **run_complete_verification.ps1** - Test runner script

### Test Configuration Files (ALL 7 VERIFIED ✅):
- ✅ **MC_4Nodes_Working.cfg** - Basic 4-node safety test
- ✅ **MC_7Nodes_Working.cfg** - 7-node safety test
- ✅ **MC_10Nodes_Working.cfg** - 10-node scalability test
- ✅ **MC_4Nodes_Byzantine.cfg** - Byzantine attack test
- ✅ **MC_4Nodes_Liveness.cfg** - Liveness properties test
- ✅ **MC_4Nodes_Partition.cfg** - Network partition test
- ✅ **MC_4Nodes_Timing.cfg** - Timing bounds test

### Documentation Files (VERIFIED ✅):
- ✅ **BOUNTY_COMPLIANCE_FINAL.md** - For comparison section
- ✅ **COUNTEREXAMPLE_ANALYSIS.md** - For debugging evidence
- ✅ **VIDEO_SCRIPT.md** - Your reading script (UPDATED ✅)
- ✅ **RECORDING_VISUAL_GUIDE.md** - Detailed what-to-show guide (NEW ✅)

### Fixed Issues:
- ⚠️ **FIXED**: VIDEO_SCRIPT.md was referencing "DAY_3_COMPLETE_REPORT.md" (removed file)
- ✅ **NOW USES**: "BOUNTY_COMPLIANCE_FINAL.md" (correct file)

---

## 🎬 YOUR RECORDING SETUP

### Physical Setup:
```
┌─────────────┐         ┌──────────────────┐
│             │         │                  │
│   PHONE     │         │     LAPTOP       │
│  (Script)   │◄───────►│  (Recording)     │
│             │  Glance │                  │
└─────────────┘         └──────────────────┘
     Left                     Center
```

### Screen Setup in Laptop:
```
┌───────────────────────────────────────────┐
│  VS Code - Tabs at Top:                   │
│  [README] [Alpenglow.tla] [MC_Byzantine]  │
│  [MC_Liveness] [MC_Timing] [MC_Partition] │
│  [BOUNTY_COMPLIANCE_FINAL]                │
│                                           │
│  Main Editor Area (Show code/config)      │
│                                           │
├───────────────────────────────────────────┤
│  PowerShell Terminal (Bottom)             │
│  PS C:\Projects\alpenglow-verifier>       │
└───────────────────────────────────────────┘
```

---

## 📱 PHONE SCRIPT NAVIGATION

### How to Use Phone Script:

1. **Open VIDEO_SCRIPT.md on phone browser or notes app**
2. **Set phone brightness to 100%**
3. **Place phone to LEFT of laptop** (easy to glance at)
4. **Keep phone unlocked** (or set screen timeout to 10 minutes)

### Reading Technique:
- Glance at phone to read 1-2 sentences
- Look at laptop screen while speaking
- Don't read word-for-word - paraphrase naturally
- If you forget, PAUSE recording, check script, RESUME

---

## 🎯 SIMPLIFIED PART-BY-PART CHECKLIST

### PART 1 (1 min) - Introduction
- [ ] Open README.md
- [ ] Zoom in: Ctrl + + + +
- [ ] Show badges at top (7/7 passing, 12 properties)
- [ ] Say: "Hello everyone! Showing Alpenglow verification..."

### PART 2 (2 min) - Running Tests
- [ ] Open PowerShell terminal
- [ ] Type: `.\run_complete_verification.ps1 -Workers 4`
- [ ] Let tests run (show output)
- [ ] Say: "All 7 tests PASSED! 100% success!"

### PART 3 (2 min) - Specification Code
- [ ] Open Alpenglow.tla tab
- [ ] Show file has 2,249 lines (bottom right)
- [ ] Scroll slowly through code
- [ ] Search: NoConflictingBlocksFinalized (Ctrl+F)
- [ ] Search: CertificateUniqueness (Ctrl+F)
- [ ] Say: "This property ensures no blockchain forks..."

### PART 4 (2 min) - Byzantine Testing
- [ ] Open MC_4Nodes_Byzantine.cfg tab
- [ ] Point at: ByzantineNodes = {n4}
- [ ] Point at: ByzantineStakeRatio = 25
- [ ] Open MC_4Nodes_Partition.cfg tab
- [ ] Say: "Even with 25% bad stake, tests passed!"

### PART 5 (1.5 min) - Timing & Liveness
- [ ] Open MC_4Nodes_Timing.cfg tab
- [ ] Point at: Delta80 = 1, Delta60 = 2
- [ ] Open MC_4Nodes_Liveness.cfg tab
- [ ] Show PROPERTIES section
- [ ] Say: "Verified timing bounds and liveness properties..."

### PART 6 (1 min) - What Makes Special
- [ ] Open BOUNTY_COMPLIANCE_FINAL.md tab
- [ ] Scroll to comparison section
- [ ] Show: 12 properties, 7 tests, 100% success
- [ ] Say: "Most competitors have 3-5 properties, we have 12..."

### PART 7 (0.5 min) - Conclusion
- [ ] Go back to terminal (show 7/7 passed)
- [ ] Go back to README.md (show badges)
- [ ] Say: "100% success rate, zero errors, thank you!"

---

## 🎥 RECORDING SOFTWARE OPTIONS

### Option 1: Windows Game Bar (Easiest)
1. Press **Win + G**
2. Click **Capture** button
3. Click **Start Recording** (or Win+Alt+R)
4. Record your screen + voice
5. Stop: Win+Alt+R again
6. Files saved in: Videos/Captures folder

**Pros**: Already installed, simple, works well
**Cons**: Can't pause recording (must stop and start new file)

### Option 2: OBS Studio (More Control)
1. Download from: obsproject.com (free)
2. Install OBS Studio
3. Add source: Display Capture
4. Add source: Audio Input Capture (microphone)
5. Click **Start Recording**
6. Can PAUSE recording (very useful!)
7. Click **Stop Recording**

**Pros**: Can pause, better quality, more control
**Cons**: Need to download and set up first

**RECOMMENDATION**: Use Windows Game Bar for quick start, or OBS if you want to pause between sections.

---

## 🎙️ VOICE RECORDING TIPS

### Before Recording:
- [ ] Drink water (clear throat)
- [ ] Close windows (reduce noise)
- [ ] Speak at 80% normal speed (slower = clearer)
- [ ] Test mic: Record 10 seconds, play back

### While Recording:
- [ ] Speak clearly and loudly
- [ ] Pause between sentences (makes editing easier)
- [ ] If mistake: STOP, wait 2 sec, say sentence again
- [ ] Don't worry about small mistakes - can edit later

### What Viewers Care About:
✅ Can they HEAR you? (volume)
✅ Can they UNDERSTAND you? (clarity)
✅ Can they SEE screen? (big text)
❌ Don't worry about: Accent, perfect grammar, small pauses

---

## ⚡ QUICK START GUIDE (15 min before recording)

1. **Open all files in VS Code** (5 min)
   - README.md
   - Alpenglow.tla
   - All 7 MC_*.cfg files
   - BOUNTY_COMPLIANCE_FINAL.md

2. **Zoom in everywhere** (2 min)
   - VS Code: Ctrl + + + + + (press 5 times)
   - PowerShell: Right-click title bar → Properties → Font size 18
   - Make text BIG and readable

3. **Turn off distractions** (2 min)
   - Close Chrome, WhatsApp, Email
   - Windows Focus Assist: ON
   - Put phone in Do Not Disturb mode

4. **Set up script on phone** (2 min)
   - Open VIDEO_SCRIPT.md on phone
   - Brightness 100%
   - Place phone on left side

5. **Test recording** (4 min)
   - Press Win+G
   - Record 30 seconds test
   - Say: "Testing one two three"
   - Stop and play back
   - Check: Can hear voice? Can see screen? Good!

**You're ready! Start recording Part 1!**

---

## 🚨 TROUBLESHOOTING

### Problem: Can't hear my voice in recording
**Solution**: 
- Check mic is not muted
- In Win+G settings, select correct microphone
- Speak louder and closer to laptop

### Problem: Screen recording is blurry
**Solution**:
- Zoom in text: Ctrl + + + +
- Use OBS Studio instead (better quality)
- Record in 1080p resolution

### Problem: I keep making mistakes
**Solution**:
- STOP recording when you make mistake
- Wait 2 seconds
- Say that sentence again from the start
- Editor can cut out the mistake part
- OR just record that whole part again (no problem!)

### Problem: Tests take too long to run
**Solution**:
- PAUSE recording after you type the command
- Let tests run in background
- Come back when tests finish
- RESUME recording to show results
- OR pre-record test output, then explain it

### Problem: I sound nervous
**Solution**:
- Remember: You're just showing your excellent work!
- Smile while speaking (makes voice sound better)
- Pretend you're explaining to a friend
- Take breaks between parts
- Reshoot if needed - no one will know!

---

## 📊 FINAL PRE-RECORDING CHECKLIST

### Files Ready:
- [ ] All files opened in VS Code tabs
- [ ] Text zoomed in (big and readable)
- [ ] PowerShell open in correct folder
- [ ] Script opened on phone

### Environment Ready:
- [ ] Room is quiet (no background noise)
- [ ] Windows Focus Assist ON (no notifications)
- [ ] Phone on Do Not Disturb
- [ ] Water bottle nearby
- [ ] Good lighting (can see screen clearly)

### Equipment Ready:
- [ ] Screen recorder tested (Win+G or OBS)
- [ ] Microphone tested (voice is clear)
- [ ] Battery charged (laptop plugged in)
- [ ] Phone charged and unlocked

### Mental Ready:
- [ ] Read script once (know what to say)
- [ ] Know which files to show when
- [ ] Feel confident (your work is excellent!)
- [ ] Ready to record (no stress, just show your work)

**ALL CHECKBOXES ✅ ? START RECORDING! 🎬**

---

## 🎯 REMEMBER

**Your Project**: 7/7 tests passing, 12 properties, 100% success
**Video Goal**: Show this excellent work in 10 minutes
**Video Result**: +5 points → 100/100 Perfect Score
**Your Advantage**: Most submissions won't have this quality

**You're not creating something new. You're showing something that already works perfectly.**

**Be proud. Be confident. GO WIN THIS BOUNTY! 🏆**

---

## 📚 REFERENCE FILES

1. **VIDEO_SCRIPT.md** - What to SAY (read from phone)
2. **RECORDING_VISUAL_GUIDE.md** - What to SHOW (detailed visual guide)
3. **This file** - QUICK REFERENCE (setup checklist)

Use all three together for best results!

**NOW GO RECORD THAT VIDEO! 💪🎬**
