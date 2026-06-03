# Initial Public Release Runbook

This runbook describes how to publish EconCSLib as a new public repository with
a clean one-commit public history while retaining the full private development
history in a separate private archive.

The target release is `v0.1.0`. The intended public repository is:

```text
https://github.com/gametheoryinlean/EconCSLib
```

Run commands from the private EconCSLib checkout unless a step explicitly says
to use the temporary public-snapshot checkout.

## Release Model

Do not change the visibility of the existing private repository directly.
Changing a private repository to public would expose its complete Git history
and its GitHub Actions history. Instead:

1. Review and commit the cleanup in the existing private repository.
2. Create an offline Git bundle as an additional backup.
3. Rename the existing private GitHub repository to
   `EconCSLib-private-archive`.
4. Create a new empty public GitHub repository named `EconCSLib`.
5. Export the reviewed private commit with `git archive`.
6. Initialize a new Git repository from that exported snapshot.
7. Push one initial public commit.
8. Verify CI, configure protection rules, and publish `v0.1.0`.
9. Archive the private GitHub repository after the public repository is known
   to work.

This preserves the full private history without publishing it. It also avoids
relying on history rewrites as a confidentiality boundary.

## Repository Roles

The release uses four GitHub repositories:

| Repository | Visibility | Purpose |
| --- | --- | --- |
| `gametheoryinlean/EconCSLib-private-archive` | private | Read-only archive of the private development history |
| `gametheoryinlean/EconCSLib` | public | Public Lean library and knowledge-source repository |
| `gametheoryinlean/blueprint` | public | Generated knowledge-blueprint site |
| `gametheoryinlean/econcslib_doc` | public | Generated Lean API-documentation site |

The public EconCSLib repository deploys generated output to the last two
repositories. Generated HTML is not committed to EconCSLib itself.

## Local Prerequisites

Install or confirm the following local tools before starting:

- `git`
- `gh` for optional GitHub CLI monitoring and release commands
- `elan`, `lake`, and the repository's configured Lean toolchain
- `python3`
- `rg`
- `mdblueprint-check` and `mdblueprint-publish`

Install the public `mdblueprint` tool into a virtual environment if it is not
already on `PATH`:

```bash
MDBLUEPRINT_HOME="$HOME/src/mdblueprint"
git clone https://github.com/gametheoryinlean/mdblueprint.git "$MDBLUEPRINT_HOME"
python3 -m venv "$MDBLUEPRINT_HOME/.venv"
"$MDBLUEPRINT_HOME/.venv/bin/pip" install -e "$MDBLUEPRINT_HOME"
export PATH="$MDBLUEPRINT_HOME/.venv/bin:$PATH"
```

Verify the commands:

```bash
command -v mdblueprint-check
command -v mdblueprint-publish
```

## Phase 1: Review the Private Cleanup

Start from the existing private checkout:

```bash
git status --short --branch
git remote -v
git diff --stat
git diff --name-status
git diff --check
```

Review the important surfaces directly:

```bash
git diff -- README.md AGENTS.md CONTRIBUTING.md CODE_OF_CONDUCT.md CITATION.cff
git diff -- .github/workflows
git diff -- EconCSLib.lean
git diff -- docs/design.md docs/maintainers docs/research
git diff -- docs/knowledge/mdblueprint.yml docs/knowledge/topics.md
```

Review new public files that are not yet tracked:

```bash
sed -n '1,240p' CONTRIBUTING.md
sed -n '1,240p' CODE_OF_CONDUCT.md
sed -n '1,160p' CITATION.cff
find .github/ISSUE_TEMPLATE -type f -print | sort
sed -n '1,200p' .github/PULL_REQUEST_TEMPLATE.md
```

Confirm that deletions match the intended cleanup:

```bash
git diff --name-only --diff-filter=D
git ls-files | rg '\.(pdf|zip|jsonl|pyc)$|(^|/)__pycache__/|^references/' || true
python3 scripts/check_lean_placeholders.py EconCSLib
rg -n 'docs/dev|PLAN\.md|\.sorry-crusher|maschler_statements' \
  README.md AGENTS.md CONTRIBUTING.md docs scripts .github EconCSLib \
  -g '!initial-public-release.md' || true
```

The artifact and private-path searches must return no matches, and the
placeholder checker must pass.

Run the local checks:

```bash
lake exe cache get
lake build
lake build EconCSLib.Examples
python3 scripts/check_lean_placeholders.py EconCSLib
python3 -m unittest tests/test_check_knowledge_references.py
python3 scripts/check_knowledge_references.py docs/knowledge
mdblueprint-check docs/knowledge --lean-root .
git diff --check
```

The placeholder checker must pass. `mdblueprint-check` should finish with
`0 error(s), 0 warning(s)`.

Build both generated documentation products once:

```bash
mdblueprint-publish docs/knowledge /tmp/EconCSLib-main-mdblueprint-site
python3 scripts/build_api_docs.py
```

Inspect the generated output:

```bash
test -f /tmp/EconCSLib-main-mdblueprint-site/graph_topics.json
test -f /tmp/EconCSLib-main-mdblueprint-site/dep_graph_document.html
test -f /tmp/EconCSLib-main-mdblueprint-site/graph.html
find /tmp/EconCSLib-main-mdblueprint-site/subgraphs/topics -name '*.json' -type f | head
find /tmp/EconCSLib-main-mdblueprint-site/node_payloads -name '*.json' -type f | head
test -f docbuild/.lake/build/doc/index.html
```

Existing Lean deprecation and linter warnings do not block the initial
release. Record them as follow-up issues rather than expanding this cleanup.

## Phase 2: Commit and Back Up the Private History

Stage the reviewed cleanup:

```bash
git add -A
git status --short
git diff --cached --stat
git diff --cached --name-status
git diff --cached --check
```

Commit it in the private repository:

```bash
git commit -m "Prepare repository for initial public release"
```

Tag the last private-history state so it is easy to locate later:

```bash
git tag -a private-history-before-public-v0.1.0 \
  -m "Private history archived before the initial public release"
```

Push the private cleanup commit to an archive-only branch and push the archive
tag before renaming the repository:

```bash
git push origin HEAD:refs/heads/archive/public-release-cleanup
git push origin private-history-before-public-v0.1.0
```

Do not push this commit to the private repository's `main` branch. The
deployment workflows run on pushes to `main`; using an archive-only branch
preserves the cleanup commit remotely without publishing generated output
before the public source repository exists.

### If GitHub rejects workflow-file updates

GitHub rejects HTTPS pushes that add or modify `.github/workflows/*.yml` when
the OAuth token does not have permission to update workflow files. The error
looks like:

```text
refusing to allow an OAuth App to create or update workflow
`.github/workflows/...` without `workflow` scope
```

The cleanup commit remains local and does not need to be recreated.

The preferred fix is to use SSH for the archive push:

```bash
ssh -T git@github.com
git remote set-url origin git@github.com:gametheoryinlean/EconCSLib.git
git remote -v
git push origin HEAD:refs/heads/archive/public-release-cleanup
git push origin private-history-before-public-v0.1.0
```

The SSH test may print a message that GitHub does not provide shell access.
That is expected when authentication succeeds.

If SSH is not configured, reauthenticate GitHub CLI over HTTPS with repository
and workflow scopes:

```bash
gh auth login --hostname github.com --git-protocol https \
  --scopes repo,workflow
gh auth setup-git --hostname github.com
gh auth status --hostname github.com
git push origin HEAD:refs/heads/archive/public-release-cleanup
git push origin private-history-before-public-v0.1.0
```

If the organization enforces SAML single sign-on, authorize the credential for
the `gametheoryinlean` organization when GitHub prompts for it.

Create a local bundle outside the repository as a second backup:

```bash
git bundle create ../EconCSLib-private-history.bundle --all
git bundle verify ../EconCSLib-private-history.bundle
```

Store the bundle somewhere private and backed up. Do not place it in the
public snapshot.

Record the exact private release-source commit:

```bash
PRIVATE_RELEASE_SHA="$(git rev-parse HEAD)"
printf '%s\n' "$PRIVATE_RELEASE_SHA"
```

Keep that terminal open or store the SHA in a private release note.

## Phase 3: Rename the Private GitHub Repository

On GitHub:

1. Open the existing private `gametheoryinlean/EconCSLib` repository.
2. Go to **Settings**.
3. In **Repository name**, enter `EconCSLib-private-archive`.
4. Click **Rename**.
5. Keep the repository private.

Update the existing local checkout immediately:

```bash
git remote rename origin private-archive
git remote set-url private-archive \
  https://github.com/gametheoryinlean/EconCSLib-private-archive.git
git remote -v
git fetch private-archive
```

GitHub redirects requests from an old repository name after a rename, but this
release intentionally reuses the old name for the new public repository.
Do not rely on the redirect. Use the explicit `EconCSLib-private-archive` URL
for the private checkout from this point onward.

Do not archive the private GitHub repository yet. Keep it writable until the
new public repository, workflows, generated sites, and release have been
verified.

## Phase 4: Create the Empty Public GitHub Repository

On GitHub:

1. Create a new repository under the `gametheoryinlean` organization.
2. Name it `EconCSLib`.
3. Set visibility to **Public**.
4. Do not initialize it with a README, `.gitignore`, license, or template.
5. Create the empty repository.

Configure basic repository metadata:

| Field | Suggested value |
| --- | --- |
| Description | `Lean 4 library and knowledge base for computational economics` |
| Website | Add the preferred project or blueprint URL after deployment |
| Topics | `lean4`, `mathlib`, `game-theory`, `economics`, `formal-verification` |

Under **Settings** > **General** > **Features**:

1. Enable **Issues**.
2. Enable **Discussions**.
3. Leave pull requests enabled.

Under **Settings** > **Actions** > **General**, confirm that GitHub Actions is
enabled for the repository.

## Phase 5: Configure Deployment Credentials

Configure deployment credentials before the first public push. That push will
run all three workflows:

- `.github/workflows/build.yml`
- `.github/workflows/blueprint.yml`
- `.github/workflows/docs.yml`

Generate two dedicated SSH key pairs outside the repository:

```bash
umask 077
KEY_DIR="$HOME/.ssh/econcslib-release"
mkdir -p "$KEY_DIR"

ssh-keygen -t ed25519 -N "" \
  -C "EconCSLib blueprint deployment" \
  -f "$KEY_DIR/blueprint"

ssh-keygen -t ed25519 -N "" \
  -C "EconCSLib API documentation deployment" \
  -f "$KEY_DIR/api-docs"
```

Use separate keys. GitHub deploy keys are repository-specific and should not be
reused across `blueprint` and `econcslib_doc`.

### Blueprint Deployment

In `gametheoryinlean/blueprint`:

1. Go to **Settings** > **Deploy keys**.
2. Click **Add deploy key**.
3. Use a descriptive title such as `EconCSLib blueprint workflow`.
4. Paste the contents of:

   ```bash
   cat "$KEY_DIR/blueprint.pub"
   ```

5. Select **Allow write access**.
6. Click **Add key**.

In the new public `gametheoryinlean/EconCSLib` repository:

1. Go to **Settings** > **Secrets and variables** > **Actions**.
2. Click **New repository secret**.
3. Name the secret `BLUEPRINT_DEPLOY_KEY`.
4. Paste the complete private-key contents from:

   ```bash
   cat "$KEY_DIR/blueprint"
   ```

5. Click **Add secret**.

### API-Documentation Deployment

In `gametheoryinlean/econcslib_doc`:

1. Go to **Settings** > **Deploy keys**.
2. Click **Add deploy key**.
3. Use a descriptive title such as `EconCSLib API docs workflow`.
4. Paste the contents of:

   ```bash
   cat "$KEY_DIR/api-docs.pub"
   ```

5. Select **Allow write access**.
6. Click **Add key**.

In the new public `gametheoryinlean/EconCSLib` repository:

1. Go to **Settings** > **Secrets and variables** > **Actions**.
2. Click **New repository secret**.
3. Name the secret `ECONCSLIB_DOC_DEPLOY_KEY`.
4. Paste the complete private-key contents from:

   ```bash
   cat "$KEY_DIR/api-docs"
   ```

5. Click **Add secret**.

Never commit these private keys. Keep the local copies in protected storage
until the deployment workflows have succeeded. Afterward, either move them
into the maintainers' credential store or securely remove the local copies.

## Phase 6: Create the One-Commit Public Snapshot

Create a separate temporary directory. Do not turn the private-history checkout
into the public checkout.

```bash
SNAPSHOT_DIR="$(mktemp -d /tmp/EconCSLib-public-snapshot.XXXXXX)"
printf '%s\n' "$SNAPSHOT_DIR"
```

Export only tracked content from the reviewed private commit:

```bash
git archive --format=tar "$PRIVATE_RELEASE_SHA" | tar -x -C "$SNAPSHOT_DIR"
cd "$SNAPSHOT_DIR"
```

Initialize a fresh repository:

```bash
git init --initial-branch=main
git add -A
git commit -m "Initial public release"
git remote add origin https://github.com/gametheoryinlean/EconCSLib.git
```

The fresh public history has one snapshot commit, so the private per-commit
attribution remains in the private archive. Public contributor credit remains
in `README.md` and `CITATION.cff`. Maintainers may add standard
`Co-authored-by:` trailers to the snapshot commit if they want GitHub to
attribute that root commit to multiple authors.

Confirm that the new repository has exactly one commit and no private-history
remote:

```bash
test "$(git rev-list --count HEAD)" -eq 1
git log --oneline --decorate --graph --all
git remote -v
```

Confirm that private and generated artifacts did not enter the snapshot:

```bash
git ls-files | rg '\.(pdf|zip|jsonl|pyc)$|(^|/)__pycache__/|^references/' || true
python3 scripts/check_lean_placeholders.py EconCSLib
rg -n 'docs/dev|PLAN\.md|\.sorry-crusher|maschler_statements' \
  README.md AGENTS.md CONTRIBUTING.md docs scripts .github EconCSLib \
  -g '!initial-public-release.md' || true
git status --short
```

The repository should be clean, the artifact/private-path searches should
return no matches, and the placeholder checker should pass.

Run the release checks in the snapshot:

```bash
lake exe cache get
lake build
lake build EconCSLib.Examples
python3 scripts/check_lean_placeholders.py EconCSLib
python3 -m unittest tests/test_check_knowledge_references.py
python3 scripts/check_knowledge_references.py docs/knowledge
mdblueprint-check docs/knowledge --lean-root .
git diff --check
```

The placeholder checker must pass. The build may emit the known Lean
deprecation and linter warnings.

## Phase 7: Push and Observe the First Public CI Run

Push the one-commit public branch:

```bash
git push -u origin main
```

The initial push should start:

| Workflow | Expected result |
| --- | --- |
| **Build Lean** | Builds the library and examples, rejects Lean placeholders, checks whitespace |
| **Build and Publish Blueprint** | Validates and renders the blueprint, then deploys `blueprint` |
| **Deploy API docs** | Builds API documentation, then deploys `econcslib_doc` |

Observe workflow runs in the GitHub Actions UI or with GitHub CLI:

```bash
gh run list --repo gametheoryinlean/EconCSLib --limit 10
```

For each active run:

```bash
gh run watch RUN_ID --repo gametheoryinlean/EconCSLib
```

If a deployment fails:

1. Read the failed step.
2. Confirm the corresponding destination repository deploy key has write
   access.
3. Confirm the matching Actions secret exists in
   `gametheoryinlean/EconCSLib`.
4. Confirm that the two deployments use different key pairs.
5. Re-run the failed workflow from the Actions UI after correcting the
   configuration.

Verify the generated sites:

```text
https://gametheoryinlean.github.io/blueprint/
https://gametheoryinlean.github.io/econcslib_doc/
```

If either site is not served yet, inspect the generated repository:

- `gametheoryinlean/blueprint` should publish from branch `gh-pages`, root
  directory.
- `gametheoryinlean/econcslib_doc` should publish from branch `main`, root
  directory.

Configure GitHub Pages under the generated repository's **Settings** >
**Pages** if needed.

## Phase 8: Protect `main`

Create the protection rule only after the first public workflow run has
completed. GitHub only offers recently reported status checks for selection.

Use a repository ruleset:

1. Open `gametheoryinlean/EconCSLib`.
2. Go to **Settings** > **Rules** > **Rulesets**.
3. Click **New ruleset** > **New branch ruleset**.
4. Name it `Protect main`.
5. Set enforcement status to **Active**.
6. Target the default branch, or include branch pattern `main`.
7. Enable **Restrict deletions**.
8. Enable **Block force pushes**.
9. Enable **Require a pull request before merging**.
10. Require at least one approving review if maintainers can satisfy that
    policy. Otherwise start with zero required approvals and increase it when
    a second active reviewer is available.
11. Enable **Require status checks to pass**.
12. Add the checks reported by the successful initial workflow runs:

    - the `build` job from **Build Lean**;
    - the `build_blueprint` job from **Build and Publish Blueprint**.

13. Enable **Require branches to be up to date before merging** if the extra
    CI run time is acceptable.
14. Optionally enable **Require linear history** if maintainers want squash or
    rebase merges only.
15. Save the ruleset.

Do not require the API-doc deployment job for pull requests:
`.github/workflows/docs.yml` intentionally deploys only after pushes to
`main`.

The blueprint workflow intentionally runs on every pull request so
`build_blueprint` is always available as a required check. Its deployment steps
remain disabled for pull requests.

Test the rule with a small pull request before announcing the release. A
documentation-only pull request is sufficient:

```bash
git switch -c test/main-protection
printf '\n' >> docs/HISTORY.md
git add docs/HISTORY.md
git commit -m "Test protected-branch workflow"
git push -u origin test/main-protection
```

Open a pull request, confirm that `build` and `build_blueprint` run, then close
the pull request without merging and delete the test branch:

```bash
git switch main
git branch -D test/main-protection
git push origin --delete test/main-protection
```

The temporary newline exists only on the closed test branch.

## Phase 9: Final Release Review

Before tagging:

1. Confirm that `main` contains the intended one-commit public snapshot.
2. Confirm all required CI checks pass.
3. Confirm both generated sites load.
4. Confirm Issues and Discussions are enabled.
5. Review the repository's public file listing.
6. Review `README.md`, `LICENSE`, `NOTICE`, `CONTRIBUTING.md`,
   `CODE_OF_CONDUCT.md`, and `CITATION.cff` in the GitHub UI.
7. Confirm `CITATION.cff` has the correct release date.

If the release happens after `2026-06-01`, update `date-released` in
`CITATION.cff` through a normal pull request before tagging.

Create a clean-clone verification checkout:

```bash
VERIFY_DIR="$(mktemp -d /tmp/EconCSLib-public-verify.XXXXXX)"
git clone --depth 1 https://github.com/gametheoryinlean/EconCSLib.git "$VERIFY_DIR"
cd "$VERIFY_DIR"
lake exe cache get
lake build
lake build EconCSLib.Examples
python3 scripts/check_lean_placeholders.py EconCSLib
python3 -m unittest tests/test_check_knowledge_references.py
python3 scripts/check_knowledge_references.py docs/knowledge
mdblueprint-check docs/knowledge --lean-root .
git diff --check
```

The placeholder checker must pass.

## Phase 10: Tag and Publish `v0.1.0`

From a clean checkout of public `main`:

```bash
git status --short --branch
git pull --ff-only origin main
git tag -a v0.1.0 -m "EconCSLib v0.1.0"
git push origin v0.1.0
```

Create a GitHub release from the tag. In the GitHub UI:

1. Open `gametheoryinlean/EconCSLib`.
2. Click **Releases**.
3. Click **Draft a new release**.
4. Select tag `v0.1.0`.
5. Use title `EconCSLib v0.1.0`.
6. Add release notes similar to:

   ```text
   Initial public release of EconCSLib.

   EconCSLib is a Lean 4 library and cross-linked knowledge base for
   computational economics, built on Mathlib. The initial release includes
   reusable infrastructure for game theory, social choice, fair division,
   matching, auctions, mechanism design, utility theory, and worked examples.

   Coverage is intentionally incomplete. Contributions, issue reports, and
   design discussion are welcome.
   ```

7. Publish the release.

The equivalent GitHub CLI command is:

```bash
gh release create v0.1.0 \
  --repo gametheoryinlean/EconCSLib \
  --title "EconCSLib v0.1.0" \
  --notes "Initial public release of EconCSLib."
```

Use the UI when publishing the initial release so the notes can be reviewed
before publication.

## Phase 11: Archive the Private GitHub Repository

After the public repository, generated sites, ruleset, and release have all
been verified:

1. Open the private `gametheoryinlean/EconCSLib-private-archive` repository.
2. Close or resolve any remaining private-only issues and pull requests.
3. Update its description to state that it is the private development-history
   archive for EconCSLib.
4. Go to **Settings**.
5. Under **Danger Zone**, click **Archive this repository**.
6. Confirm the archive operation.

Archiving makes the private repository read-only while retaining branches,
tags, commits, issues, pull requests, and settings. Keep the private bundle
backup as an independent recovery path.

## Phase 12: Seed Public Work

Create focused public issues after the release. Keep each issue contribution
sized and link the relevant blueprint nodes.

Suggested initial backlog:

1. Implement expected-utility representation and positive-affine uniqueness.
2. Formalize generic stable-matching existence.
3. Complete the Bondareva-Shapley and convex-core theorem suite.
4. Complete Shapley-value efficiency, uniqueness, and convex-core membership.
5. Prove that dominance-solvable games have a unique Nash equilibrium.
6. Complete the Robinson, Cesaro-average, and fictitious-play convergence
   results.
7. Reduce Lean deprecation and linter warnings.
8. Narrow broad imports where this is straightforward.

Create a welcome discussion explaining that incomplete coverage is expected in
the initial release and that design feedback, theorem proposals, and
contributions are welcome.

## Rollback and Incident Handling

### Before the first public push

Delete the temporary snapshot and recreate it from the reviewed private SHA.
Do not modify the private-history archive to repair a snapshot-only mistake.

### After a public push but before announcement

Assume any pushed content has already been copied. Rewriting Git history does
not remove exposed information from other clones or caches.

If an ordinary file is wrong:

1. Fix it through a normal commit or pull request.
2. Re-run CI.
3. Tag only after the corrected public `main` is clean.

If confidential material or a credential is exposed:

1. Rotate or revoke the credential immediately.
2. Remove the file from the public repository.
3. Follow GitHub's sensitive-data-removal procedure if history cleanup is
   required.
4. Re-check generated sites and workflow artifacts for copies.

### After `v0.1.0`

Do not move the `v0.1.0` tag. Publish corrections as normal commits and issue
`v0.1.1` when appropriate.

## GitHub Documentation

- [Creating a new repository](https://docs.github.com/en/repositories/creating-and-managing-repositories/creating-a-new-repository)
- [Renaming a repository](https://docs.github.com/en/repositories/creating-and-managing-repositories/renaming-a-repository)
- [Archiving repositories](https://docs.github.com/en/repositories/archiving-a-github-repository/archiving-repositories)
- [Enabling repository features](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/enabling-features-for-your-repository)
- [Enabling GitHub Discussions](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/enabling-features-for-your-repository/enabling-or-disabling-github-discussions-for-a-repository)
- [Managing deploy keys](https://docs.github.com/en/authentication/connecting-to-github-with-ssh/managing-deploy-keys)
- [Using secrets in GitHub Actions](https://docs.github.com/en/actions/how-tos/write-workflows/choose-what-workflows-do/use-secrets)
- [Creating repository rulesets](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets/creating-rulesets-for-a-repository)
- [Troubleshooting required status checks](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/defining-the-mergeability-of-pull-requests/troubleshooting-required-status-checks)
- [Managing releases](https://docs.github.com/en/repositories/releasing-projects-on-github/managing-releases-in-a-repository)
