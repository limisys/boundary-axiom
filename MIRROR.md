# Mirror policy

- **Canonical:** <https://github.com/limisys/boundary-axiom>
- **Mirror:** <https://gitee.com/limisys/boundary-axiom> (read-only)

The Gitee repository is a mirror for readers in mainland China. It must contain
the same commit and the same tags as GitHub. Do not create Gitee-only commits,
branches, or releases.

## Sync (maintainer)

```bash
git push origin main --follow-tags
GIT_SSH_COMMAND='ssh -i ~/.ssh/id_gitee -o IdentitiesOnly=yes' \
  git push gitee main --follow-tags
```

Verify that both remotes point at the same commit:

```bash
git ls-remote origin refs/heads/main refs/tags/v1.0.0
git ls-remote gitee  refs/heads/main refs/tags/v1.0.0
```

If Gitee ever diverges: confirm there are no Gitee-only commits, then reset the
mirror to the GitHub commit with `--force-with-lease`. Never merge Gitee-only
changes back into GitHub.

Issues and pull requests belong on GitHub. The Gitee mirror is not a second
source of truth.
