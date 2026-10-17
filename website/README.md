# Control Systems Suite

An interactive web app for classical control analysis: **Routh stability**, **Root Locus**, and **Bode plots**. It runs entirely in the browser, with no backend and no math libraries. Built with React (Create React App) and plain SVG.

**Live demo:** https://Mohammed-Nasr-Aldin.github.io/System-Stability/

---

## Features

### Routh-Hurwitz stability
- Characteristic equation of any order (up to 30).
- Full Routh table with the special cases handled:
  - A zero in the first column is replaced by a small epsilon.
  - A zero row is replaced by the derivative of the auxiliary polynomial A(S), and its roots are shown.
- Counts the poles in the RHP, on the jω axis, and in the LHP.
- Flags repeated poles on the jω axis as unstable.
- Cross-checks the Routh result against the numerical roots.
- **Gain mode:** enter coefficients such as `K+2` or `2K` to get the stable K ranges and the critical K values (with the oscillation frequency), plus a slider to see the Routh table at any K.

### Root Locus
- Takes the numerator order, the denominator order, the coefficients, and the gain K.
- Computes poles, zeros, asymptotes (centroid and angles), real-axis segments, break-away and break-in points, angles of departure and arrival, and jω-axis crossings.
- Gives the stability condition as a range of K.
- A K slider moves the closed-loop poles along the locus live.
- On the plot, **x = open-loop poles** and **o = open-loop zeros**.

### Bode plot
- Magnitude and phase plots with the asymptotes drawn on top.
- Slope labelled on every segment, with the final roll-off.
- **UGF** and **GBW**.
- **GX / PM** (gain crossover and phase margin in degrees) and **PX / GM** (phase crossover and gain margin in dB).
- Closed-loop stability under unity feedback.

### Interaction
- Zoom with the mouse wheel or by pinching, drag to pan, plus zoom buttons and a reset button.
- Every graph can be downloaded as a high-resolution PNG.
- Responsive layout for phones and tablets.
- Inputs accept numbers and expressions such as `1/3`, `2*pi`, `1e3`. Invalid input is highlighted with a message.
- Built-in examples for every mode.

---

## Available Scripts

In the project directory (`website`), you can run:

### `npm start`
Runs the app in development mode.\
Open [http://localhost:3000](http://localhost:3000) to view it in your browser. The page reloads when you make changes.

### `npm run build`
Builds the app for production into the `build` folder. The build is minified and ready to deploy.

---

## Project structure

```
System-Stability/
├── .github/workflows/deploy.yml   # GitHub Pages deployment
└── website/
    ├── public/
    │   ├── index.html
    │   └── favicon.svg
    ├── src/
    │   ├── App.js                 # all the app logic and UI
    │   └── index.js
    ├── src/index.css              # styles
    └── package.json
```

---

## Deploy to GitHub Pages

1. In `website/package.json`, set `homepage` to your Pages URL:
   ```json
   "homepage": "https://Mohammed-Nasr-Aldin.github.io/System-Stability"
   ```
2. In the repository go to **Settings → Pages → Build and deployment → Source** and choose **GitHub Actions**.
3. Push to `main`. The workflow in `.github/workflows/deploy.yml` builds the app and publishes the `website/build` folder.

Follow the progress in the **Actions** tab. When the run is green, the site is live.

---

## Notes on accuracy
- Polynomial roots are found with the Aberth-Ehrlich method (double precision).
- Tolerances scale with the size of the coefficients, so very large or very small systems behave consistently.
- Near the jω axis, numerical roots can differ slightly from the exact result. The app warns you when the Routh count and the root count disagree.
- Gain mode gives exact critical K values when the coefficients are linear in K, and uses scanning with bisection otherwise.

---

## Tech stack
- React 18 (Create React App)
- Plain SVG for all plots
- Plain CSS, no UI library

---

© 2026 Mohammed Nasr Eldin