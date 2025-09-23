# Alpenglow Verifier

**A machine-checkable formal verification system for Solana’s Alpenglow consensus protocol.**

This project provides a formal verification system for Alpenglow, modeling its core components in TLA+ and verifying critical safety, liveness, and resilience properties. It includes an interactive web interface to configure models, inspect specifications, and analyze counterexamples with AI-powered assistance.

## Table of Contents
1.  [Project Overview](#project-overview)
2.  [Features](#features)
3.  [Getting Started](#getting-started)
    *   [Prerequisites](#prerequisites)
    *   [Installation](#installation)
    *   [Running the Application](#running-the-application)
4.  [Project Structure](#project-structure)
5.  [Technical Report Summary](#technical-report-summary)
6.  [Video Walkthrough Script](#video-walkthrough-script)
7.  [License](#license)

---

## Project Overview

The Alpenglow Verifier is a tool designed to rigorously analyze the correctness of the Alpenglow consensus protocol. By leveraging formal methods (TLA+), we can exhaustively check the protocol's logic against a set of formally defined properties, identifying subtle bugs, race conditions, and edge cases that are difficult to find through traditional testing.

This application serves as the front-end for that verification effort, making the formal models and their results accessible and understandable.

## Features

-   **Interactive TLA+ Viewer**: Browse the formal specification of Alpenglow's components.
-   **Formal Property Definitions**: Inspect the safety, liveness, and resilience properties being checked.
-   **Model Configuration**: Set up verification runs with different network sizes and adversarial conditions.
-   **Counterexample Analysis**: Interactively step through failure traces produced by the TLC model checker.
-   **AI-Powered Explanation**: Get human-readable explanations and suggested fixes for TLA+ specification errors from Genkit.

## Getting Started

Follow these instructions to set up and run the project locally.

### Prerequisites

-   Node.js (v18 or later)
-   npm (or a compatible package manager)

### Installation

1.  **Clone the repository:**
    ```bash
    git clone <your-repository-url>
    cd alpenglow-verifier
    ```

2.  **Install dependencies:**
    ```bash
    npm install
    ```

3.  **Set up environment variables:**
    Create a `.env` file in the root directory and add your Google AI API key:
    ```
    GEMINI_API_KEY=your_api_key_here
    ```

### Running the Application

1.  **Start the Genkit services:**
    In a separate terminal, run:
    ```bash
    npm run genkit:watch
    ```

2.  **Start the development server:**
    ```bash
    npm run dev
    ```

Open [http://localhost:9002](http://localhost:9002) in your browser to see the application.

## Project Structure

-   `src/app/`: Contains the Next.js pages and layouts for the application.
-   `src/components/`: Reusable React components used throughout the UI.
-   `src/ai/`: Home to the Genkit flows and AI-related logic.
-   `src/lib/`: Utility functions and mock data.
-   `Alpenglow.tla`: (Example file) The TLA+ specification for the protocol.
-   `properties.tla`: (Example file) Formal property definitions.

---

## Technical Report Summary

### 1. Introduction
This report details the formal verification of the Alpenglow consensus protocol using TLA+. Our goal is to provide machine-checkable proofs of Alpenglow’s key safety, liveness, and resilience properties.

### 2. Formal Model
We developed a TLA+ specification that models the following components:
-   **Votor**: The dual-path consensus mechanism, including the fast (≥80% stake) and conservative (≥60% stake) paths.
-   **Rotor**: The erasure-coded block propagation mechanism, modeled as an abstract message-passing system.
-   **Certificates**: The logic for generating, aggregating, and verifying certificates of finality.
-   **State Management**: Leader rotation, slot advancement, and timeout handling.

### 3. Verified Properties
We formally defined and verified the following properties under various network configurations:

-   **Safety**:
    -   **Theorem**: No two conflicting blocks can be finalized in the same slot.
    -   **Status**: Verified for models up to 10 nodes with 1 Byzantine node.
-   **Liveness**:
    -   **Theorem**: The network eventually finalizes new blocks if at least 60% of the stake is honest and responsive.
    -   **Status**: Verified.
-   **Resilience**:
    -   **Theorem**: Protocol safety holds with up to 20% of the total stake controlled by Byzantine actors.
    -   **Status**: Verified.

*Note: This is a summary. Full proof outcomes are available in the `results/` directory.*

---

## Video Walkthrough Script

**(Scene: Opening shot of the Alpenglow Verifier dashboard)**

**Narrator**: "Welcome to the Alpenglow Verifier—a tool for formally verifying the correctness of Solana's Alpenglow consensus protocol. In this video, we'll walk through how it works."

**(Cut to: Specification page)**

**Narrator**: "Here on the **Specification** page, you can see the complete TLA+ model of Alpenglow. We've broken it down into modular components like Votor, Rotor, and the certificate logic to make it easier to understand."

**(Cut to: Properties page)**

**Narrator**: "The **Properties** page defines what we're trying to prove. We've formalized key guarantees, like 'no conflicting blocks can be finalized' (Safety) and 'the network always makes progress' (Liveness)."

**(Cut to: Dashboard, user fills out the form)**

**Narrator**: "To start a verification run, you can configure a model on the **Dashboard**. You can set the network size, the number of Byzantine nodes, and choose from different adversarial scenarios."

**(Cut to: Verification Runs page, showing a 'Failed' run)**

**Narrator**: "The **Verification Runs** page shows the results. Here, we see a run has failed. Let's find out why."

**(Cut to: Analysis page)**

**Narrator**: "The **Analysis** page is where we debug. On the left, we have the step-by-step trace that led to the failure. On the right, we have a visualization of the network state at each step."

**(Narrator clicks "Get Explanation")**

**Narrator**: "But the real power comes from the AI-powered explanation. By clicking this button, the system sends the specification and the counterexample to an AI, which analyzes the trace and provides a human-readable explanation of what went wrong and how to fix it."

**(Scene: AI explanation appears)**

**Narrator**: "As you can see, the AI identified a potential equivocation issue and is suggesting a specific change to our TLA+ spec. This allows us to rapidly debug and strengthen the protocol's design."

**(Scene: Closing shot of the dashboard)**

**Narrator**: "The Alpenglow Verifier combines formal methods with AI to make building reliable distributed systems faster and more accessible. To learn more, check out our documentation on GitHub. Thanks for watching!"

---

## License

This project is licensed under the Apache 2.0 License. See the [LICENSE](LICENSE) file for details.
