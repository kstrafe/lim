# Landing page

`index.html` and `site.css` are a buildless GitHub Pages site. There are no
JavaScript, font, math-rendering, package, or CDN dependencies. The limit
notation is styled text with an accessible spoken label.

To publish, configure the repository's GitHub Pages source to serve the
`docs` directory from the branch containing these files. No workflow or
custom domain is required. Asset URLs are relative, so project sites work
under a repository subpath as well as at a domain root.

In GitHub: **Settings → Pages → Build and deployment**, choose **Deploy
from a branch**, then select your publishing branch and **/docs**. Save.
The `.nojekyll` marker tells Pages to serve these files without Jekyll.
Publishing is configured in GitHub; creating these files does not enable
hosting by itself.

To preview locally, serve `docs` with any static HTTP server, or open
`docs/index.html` directly in a browser.

The page intentionally presents near-zero compilation and execution time as
an engineering aspiration, not a measured performance guarantee. The code
sample is a complete program and should compile with an exit status of 42.
The downloadable `answer.lim` is the same program shown on the page.
Keep both in sync with canonical language syntax when changing the compiler.
