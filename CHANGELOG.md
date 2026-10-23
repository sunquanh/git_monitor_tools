# 变更日志

本文件由 git-cliff 依据提交历史自动生成（配置见仓库根目录 cliff.toml），请勿手工编辑。

## [未发布]

### ✨ 新功能

- 新增关页自动退出：以 SSE 连接数为页面存活信号，最后一个页面关闭且宽限期（默认10s）内无新连接则 cleanup 后退出；设置页加开关；启动.bat 正常退出（码0）直接关窗、异常才 pause

- 新增：工作台「💻 终端」按钮——在当前仓库目录打开系统终端（Win/macOS/Linux，路径仅取服务端配置防注入）

- 新增：Amend 修正提交 + Conventional Commits 结构化输入（type/scope）


### 🐛 问题修复

- 再修终端按钮 Windows 闪退：cmd /k 直连时 stdin 被重定向到空设备会读 EOF 秒退，改经 start 启动（独立 argv 传参，兼避引号转义坑）

- 修复终端按钮在 Windows 上报错「找不到 '\\' 文件」：去掉 cmd /c start 整串拼接，改 cmd /k + 路径独立 argv（list2cmdline 转义引号是根因）

- 修复审查发现的3个问题：amend空消息改用 --no-edit 沿用原提交信息；设置页补网络超时(net_timeout)入口；审计日志与配置备份加入 .gitignore


### 📚 文档

- 优化版本说明


### 📦 其他变更

- Update README.md

- Add files via upload

- Add files via upload

- Create 1.txt

- Create redme.txt

- Add files via upload

- Initial commit


### 🚀 优化改进

- 优化版本

- UI 与功能优化修复：对比度/版本号/README/线程安全/示例配置


### 🧹 清理

- 删除误上传的空文件 web/vendor/1.txt

- 删除误上传的空文件 web/redme.txt


