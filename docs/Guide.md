1. Install elan, codex, git, python

2. Add script

   ```bash
   git clone https://github.com/yuanyi-350/TongWen_script
   mv TongWen_script/* .
   mv TongWen_script/.codex .
   rm -rf TongWen_script/
   ```

3. Setup email, 

   (1) test with `python3 -m tests.test_send_email`

   (2) **Add `email_config.toml` to `.gitignore`** !!!

4. Codex Settings

   (1) Grant Codex permissions and trust this directory.

   (2) Install `lean-lsp-mcp` by copy `.codex/config.toml`

   (3) Test by `/mcp` in codex.

   ```bash
   /mcp
   
   🔌  MCP Tools
   
     • lean_lsp
       • Status: enabled
       • Auth: Unsupported
       • Command: uvx lean-lsp-mcp
       • Cwd: /home/yuanyi/Documents/Lean/SardMoreira
       • Env: LEAN_LOG_LEVEL=*****, LEAN_PROJECT_PATH=*****
       • Tools: lean_build, lean_code_actions, lean_completions, lean_declaration_file, lean_diagnostic_messages, lean_file_outline, lean_get_widget_source, lean_get_widgets, lean_goal,
   lean_hammer_premise, lean_hover_info, lean_leanfinder, lean_leansearch, lean_local_search, lean_loogle, lean_multi_attempt, lean_profile_proof, lean_references, lean_run_code,
   lean_state_search, lean_term_goal, lean_verify
       • Resources: (none)
       • Resource templates: (none)
   
   ```

5. Lean Settings

   (1) Use prompt in [VersionSync_PROMPT.md](docs/VersionSync_PROMPT.md) to update version,

   (2) Run `ln -s ../.global_lake .lake` in terminal.

   (3) Test the setup by running `lake exe cache get` and `lake build Mathlib`.

6. Git Settings

   (1) Fork the repo and change `git remote -v`

   (2) Test `git push`

   (3) Add `.log` to `.gitignore`

7. setup `WORKERS` environment variable and run `python3 pipeline.py --dir Optlib`
