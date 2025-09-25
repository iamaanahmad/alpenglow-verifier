# Contributing to Enhanced Alpenglow Formal Verification

We love your input! We want to make contributing to Enhanced Alpenglow Formal Verification as easy and transparent as possible, whether it's:

- Reporting a bug
- Discussing the current state of the code
- Submitting a fix
- Proposing new features
- Becoming a maintainer

## 🚀 Quick Start for Contributors

### Prerequisites
- Java 11+ (for TLA+ model checker)
- PowerShell 5.1+ (for automation scripts)
- Node.js 18+ (for web interface)
- Git

### Development Setup
```bash
# Fork and clone the repository
git clone https://github.com/iamaanahmad/alpenglow-verifier.git
cd alpenglow-verifier

# Install dependencies
npm install

# Run basic verification test
java -jar tla2tools.jar -config MC_4Nodes.cfg MC_4Nodes.tla

# Start web interface (optional)
npm run dev
```

## 🔬 Types of Contributions

### 1. **Formal Verification Improvements**
- New TLA+ properties and invariants
- Performance optimizations for model checking
- Enhanced Byzantine behavior modeling
- Statistical sampling improvements

### 2. **Documentation**
- Tutorial improvements
- Code comments and explanations
- Best practices guides
- Translation efforts

### 3. **Web Interface**
- UI/UX improvements
- New visualization features
- AI-powered analysis enhancements
- Accessibility improvements

### 4. **Testing & Quality**
- New test configurations
- Bug fixes and error handling
- Performance benchmarking
- Code quality improvements

## 📝 Development Process

We use GitHub Flow, so all code changes happen through pull requests:

1. **Fork** the repo and create your branch from `main`
2. **Make changes** and add tests if applicable
3. **Test thoroughly** using our verification suite
4. **Update documentation** if needed
5. **Submit a pull request**

### Branch Naming Convention
- `feature/description` - New features
- `fix/description` - Bug fixes
- `docs/description` - Documentation updates
- `perf/description` - Performance improvements

## 🧪 Testing Guidelines

### Before Submitting
```bash
# Run comprehensive verification
./verify_comprehensive.ps1

# Test specific configurations
java -jar tla2tools.jar -config MC_4Nodes.cfg MC_4Nodes.tla
java -jar tla2tools.jar -config MC_Byzantine_Test.cfg MC_Byzantine_Test.tla

# Generate verification report
./generate_verification_report.ps1
```

### TLA+ Code Standards
- Use clear, descriptive variable names
- Add comments for complex logic
- Follow existing formatting conventions
- Ensure all properties are well-documented

### PowerShell Script Standards
- Use proper error handling
- Include progress indicators
- Follow PowerShell best practices
- Test on Windows environments

## 📋 Pull Request Process

1. **Update the README.md** with details of changes if applicable
2. **Update documentation** in the `docs/` folder
3. **Add tests** for new functionality
4. **Ensure all tests pass** before submitting
5. **Request review** from maintainers

### Pull Request Template
```markdown
## Description
Brief description of changes

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Documentation update
- [ ] Performance improvement

## Testing
- [ ] All existing tests pass
- [ ] New tests added for new functionality
- [ ] Manual testing completed

## Verification Results
- Configuration tested: [e.g., MC_4Nodes, MC_Byzantine_Test]
- Properties verified: [list any new properties]
- Performance impact: [describe any performance changes]
```

## 🐛 Bug Reports

Great bug reports tend to have:

- **Quick summary** and/or background
- **Steps to reproduce** - be specific!
- **What you expected** would happen
- **What actually happens**
- **Sample code** or configuration files
- **Environment details** (OS, Java version, etc.)

### Bug Report Template
```markdown
**Environment:**
- OS: [e.g., Windows 11]
- Java Version: [e.g., OpenJDK 17]
- PowerShell Version: [e.g., 5.1]

**Description:**
A clear description of the bug.

**Steps to Reproduce:**
1. Run command: `...`
2. See error: `...`

**Expected Behavior:**
What should have happened.

**Actual Behavior:**
What actually happened.

**Additional Context:**
Any other relevant information.
```

## 💡 Feature Requests

We love feature requests! Please provide:

- **Use case** - why is this feature needed?
- **Proposed solution** - how should it work?
- **Alternatives considered** - what other approaches did you think about?
- **Additional context** - mockups, examples, etc.

## 🏆 Recognition

Contributors will be:
- Listed in our README
- Mentioned in release notes
- Invited to join our Discord community
- Considered for maintainer roles

## 📚 Resources

### Learning TLA+
- [TLA+ Official Documentation](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+ Tutorial](https://learntla.com/)
- [TLA+ Examples](https://github.com/tlaplus/Examples)

### Understanding Alpenglow
- [Alpenglow Whitepaper](https://solana.com/alpenglow)
- [Verification Methodology](./docs/verification_methodology.md)
- [Our Verification Methodology](./docs/verification_methodology.md)

### Development Tools
- [TLA+ Tools](https://github.com/tlaplus/tlaplus)
- [VS Code TLA+ Extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus)
- [PowerShell Documentation](https://docs.microsoft.com/en-us/powershell/)

## 📞 Getting Help

- **Discord**: Join our community server
- **GitHub Issues**: For bugs and feature requests
- **GitHub Discussions**: For questions and general discussion
- **Email**: iamaanshaikh@cit.org.in for private matters

## 📄 License

By contributing, you agree that your contributions will be licensed under the Apache 2.0 License.

---

**Thank you for contributing to the future of consensus protocol verification!** 🚀