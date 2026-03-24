#!/bin/bash

set -e # 设置遇到错误立即停止

GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

append_to_gitignore() {
    local entry="$1"

    if grep -Fxq "$entry" .gitignore 2>/dev/null; then
        echo "$entry 已存在于 .gitignore 中。"
        return
    fi

    printf '%s\n' "$entry" >> .gitignore
    echo "已将 $entry 添加到 .gitignore。"
}

append_to_gitignore "email_config.toml"
append_to_gitignore ".log"
append_to_gitignore "__pycache__"


echo -e "\n${GREEN}[2/7] 拉取 TongWen_script 脚本...${NC}"
if [ -d "TongWen_script" ]; then
    rm -rf TongWen_script
fi
git clone https://github.com/yuanyi-350/TongWen_script

shopt -s dotglob # 开启 dotglob，让 * 也能匹配到类似 .gitignore, .codex 这样的隐藏文件
mv -n TongWen_script/* . 2>/dev/null || true # 使用 -n 参数移动，遇到同名文件直接跳过不覆盖
shopt -u dotglob # 恢复 dotglob 的默认设置

if [ -d "TongWen_script/.codex" ]; then
    mv TongWen_script/.codex .
fi
rm -rf TongWen_script/
echo "文件移动完成。"

CURRENT_DIR=$(pwd)
if [ -f ".codex/config.toml" ]; then
    # 使用 | 作为 sed 的分隔符，替换路径
    sed -i.bak "s|/root/_________________|$CURRENT_DIR|g" .codex/config.toml
    rm -f .codex/config.toml.bak # 删除备份文件
    echo -e "${GREEN}已自动将 .codex/config.toml 中的路径更新为: $CURRENT_DIR${NC}"
else
    echo -e "${YELLOW}警告: 未找到 .codex/config.toml，跳过路径替换！${NC}"
fi



echo -e "\n${GREEN}[3/7] 配置 Email 设置...${NC}"

cp ../email_config.toml . # 依赖当前环境配置
echo "正在测试发送邮件..."
uv sync
uv run python3 -m tests.test_send_email





echo "输入 '/mcp' 测试是否看到 lean_lsp 状态为 enabled"
echo -e "${YELLOW}>>> Use prompt in [VersionSync_PROMPT.md](docs/VersionSync_PROMPT.md) to update version${NC}"
codex




echo -e "\n${GREEN}[5/7] Lean 环境配置...${NC}"
read -p "当你更新完这三个文件后，按 [Enter] 键继续执行后续 Lean 命令..." 

rm -rf .lake
ln -s ../.global_lake .lake
echo "已执行: ln -s ../.global_lake .lake"

echo "正在执行 lake exe cache get..."
lake exe cache get
echo "正在执行 lake build Mathlib..."
lake build Mathlib





echo -e "\n${GREEN}[6/7] Git 仓库配置...${NC}"
git remote -v
read -p "请输入你 Fork 后的仓库地址 [留空则跳过]: " FORK_URL
if [ -n "$FORK_URL" ]; then
    git remote set-url origin "$FORK_URL"
    echo "已将 git remote 修改为 $FORK_URL"
fi

echo "测试推送到远程库..."
git add .
git status
echo "请执行 git commit -m "init commit" && git push"
