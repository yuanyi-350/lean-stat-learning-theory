1. 修改`lean-toolchain`,`lake update -R` 
1. 将 `.lake` 里面的软连接共用, 避免占用磁盘空间爆炸
2. 拓扑排序, 从底层向上修 (现在已经设计了完善的并行算法) 
3. 按照拓扑排序的顺序, 每次选取一个文件, 让codex修改, 直到这个文件可编译.
3. 对于每个文件, 指示codex从上往下一个错一个错的修 
4. 继续下一个文件.



成果 : 把 [README.md](README.md) 里的仓库基本上完成了升级, 平均每个仓库花费不超过2块钱 (codex 便宜号池), 平均每个仓库 $\le 2M$ , 

局限 : 仓库里不能有 `sorry` , 并且单个文件不要超过 1500 行

TODO

1. 核查语义一致性, [例子](https://github.com/yuanyi-350/ray/commit/eb5bf56b8decf3b7b85732483028449f2d8c3985)

   (1) 提取修改哪些 statement

   (2) 判断是否改变语义

   (3) 如果发现作弊, 则重新升级这个 statement.

2. Benchmark

   (1) 保留 codex 思维链的 log, 类似FATE的评测方法, 根据思维链长短判断难度

   (2) 记录下pipeline里报错文件

3. 如何查理 `sorry` 和 `merge conflict` [例子](https://github.com/yuanyi-350/SardMoreira/commit/efdca891ece842b56fb278b33e64836b863b0a54)

   (1) 预处理, 把含 `sorry` 的命题注释掉, 再走原先pipeline

   (2) 潜在问题, 可能会有定理依赖 `sorry` (比如很多现代定理会依赖黎曼猜想)

   (3) 原先仓库的定理被 `merge` 到 mathlib 中, 出现重名.

4. Localy 修改 (如果要考虑给 lean-community 用的话)

   (1) 和gnl进行了交流, 他认为 : 最低要求是能跑就行，正常要求是每个报错只修改前后3行，总行数增加不超过5. 这样可以避免AI审美的问题. 

   (2) 现在虽然加入PROMPT进行限制, 但是效果仍不理想, 时常会大段大段的重写. [例子](https://github.com/yuanyi-350/optlib/commit/fe51e65f57cd7988b9349885250a859a437e39be) , [例子](https://github.com/yuanyi-350/SardMoreira/commit/db2fadb4a7ca7281d140a89959df87a478083631) 第二个例子何意味?

   (3) 解决方案 1. 加入一个 golf agent (和 xrh 学姐的mathlib taste调研相关)

   (4) 解决方案 2. 注意到Lean是一种函数式编程语言, 每一步负责把一个goal状态转移到另一个goal状态.

   比如升级后 `tac` 导致报错, 但是在原版本完美 fit . 我们可以收集原版本中 `tac` 前后的状态 $A \to$ `tac` $\to B$

   然后在新的版本中, 只需用强大的prover证明 $A \to B$ 这个命题即可.

   `tac` 状态收集需要 statement正确, 但是在 `have` 嵌套时提取/修改statement是灾难性的, 需要先用 codex完成statement修改, 准确度可能不高/误伤? 这会极大的提高pipeline复杂度, 造成维护问题.

   缺陷 : 

   1. 每个仓库需要重新clone一遍lake, 磁盘空间爆炸, 不利于服务器上跑. (一个仓库 1G) 
   2. codex的自主性可以golf proof (避免重复造轮子) , [例子](https://github.com/yuanyi-350/optlib/commit/9e89ba9fb0e46fb262024f9119c4d6ef58142a4b) 

   好处 : 

   1. 可以明显的节省token , 省时省钱!  但是前提是合理并行/拆分, 比如一个thm可能有数十个错误. 这意味着要数十次迭代.

   2. 更容易locally修改

5. (1) 服务器上批量运行的监控系统, pipeline出现错误时发邮件提醒 / openclaw 盯盘 (贵)

   (2) 加snapshot

6. 对于独立仓库已经有pipeline, 对于mathlib PR需要给出一套解决方案
