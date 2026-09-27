# 引用結果をLean入力へ切り出す境界

Date: 2026-09-21
Agent: Codex / root

[CITATION-REGISTER](../CITATION-REGISTER.md)の文献照合を受けた実装方針。
以下は新しいLean宣言の実装や証明を報告する表ではない。既存の実装は
[EXTERNAL-INPUTS](../EXTERNAL-INPUTS.md)と[PART-I](../PART-I.md)を正とする。
引用されているだけで、その文献の全定理を外部仮定に追加しない。

| 範囲 | 切り出せる既知の結果と出典 | 入力に保持する仮定・規約 | 本稿側で証明・照合するもの |
|---|---|---|---|
| 共通・GH | BBI7.3.25、Tuzhilin6.12,7.18,7.19,7.24 | 非空コンパクト等長類、対応の歪みの半分、通常のGH距離 | 固定したLeanのGH定義との同定、有限網の選択、構成する写像の評価 |
| 共通・共通実現 | Gromov§6、Villani著者原稿27.2 | 共通コンパクト実現とmetric gluingの範囲を区別 | 収束列の反復gluing・全有界性・完備化。引用だけで列全体の所要模型を得たことにしない。2026-09-22には別経路のKhezeli v5 Lemma2.5＋Example2.19を照合し、収束版をGHCommonEmbeddingInputとして採用 |
| 共通・基礎解析 | Beer Exercises2.2.11/3.2.9、Muscat6.26、Cobzaș1.3.33/1.3.38、Engelking2.1.8 | 非空コンパクト超空間、距離化可能性、局所有限support、正規性・閉集合 | 実際の被覆・関数族への適用。対応するmathlib定理を使えるなら重複した外部仮定は作らない |
| 共通・測度 | Bogachev7.10.4/7.10.5,8.2.3/8.2.4,7.1.7,8.9.3/8.9.4、Parthasarathy III.1.1、Shioya1.12/1.13/1.15 | Radon確率、弱位相、可分/Polish/コンパクトの各必要条件、Prokhorov規約 | barycenter、押し出し、台の議論と距離規約の接続。既存Part Iの証明は保持 |
| I・GHP | Khezeli v5 Thms2.6/2.12, Lemma2.5, Example2.1(iii), Lemmas2.8/2.13 | 空間全体の測度保存等長同型、max規約、確率測度、所要の連続性 | 実装済みGHPMetricInput/GHPPolishInput/GHPCommonEmbeddingInputの接続。近似確率はLemma2.13＋Remarks2.14(ii)/2.15の明示的入力。開射影や不変liftは別証明として実装済み |
| I・Haar | Diestel–Spalsbury5.14, Chapter5§3、BBI1.6.14 | コンパクト群、正規化、両側不変性。コンパクト自己等長埋込の全射性 | 不変全台確率の構成、平均、自然性。既存Lean証明を使い、選択の空間依存連続性をHaar定理へ含めない |
| I・Valov | arXiv v2 Theorem1.1 | 完全距離化可能空間間の連続開全射、Radon確率、弱位相。コンパクト台制限を追加しない | 確率上のsoftnessから右逆を得てDiracと合成する特殊化、射影の開性、全台化・平均・自然性。Polish特殊化の入力型とDirac合成・fiberへの集中は実装済み。実際の不変GHP部分空間への適用も完了。carrierへの輸送・平均の自然性・変動carrierでのfiber輸送まで実装。joint閉定義域上のfamily平均の収束も実装。既存選択との同定と任意収束列への適用も接続し、Type 0のモデルで同じ選択のM1・M2・M3を証明。retractの系も全台・不変全台の制限を含め証明。D(X) API・全universeへの同じ選択の移送・GHP等長同型・全universeのretractまで完了。平均作用素の注記も証明。Part Iの全ラベル対応はPART-I-INVENTORY.json |
| II・Lp最良近似 | Breit–Gmeineder3.2.36(b),5.6.1 | 非空閉凸集合、一様凸Banach空間。Lpの指数範囲と実/複素体 | 本稿の有限次元部分空間の閉性、全台確率による単射性、一意最小化元のパラメータ依存 |
| II・作用素基礎 | Muscat14.19/15.22、Maria–Oudot–Solomon Def11/Props12–13、Breit–Gmeineder3.2.27/2.8.20(a) | compact/self-adjoint、複素Banachと実Hilbertの使い分け、Fubiniの可積分性 | 距離kernel固有の積分評価とC(X)/L2間の同定 |
| II・スペクトル摂動 | Anselone–Palmer5.3/6.3/§7 p.429 | 複素Banach、強収束、差のcollective compactness、resolvent内の輪郭と向き・巻数、有限次元性の条件 | 変動する距離空間を共通作用素模型へ移す構成、collective compactness、Riesz像と所要実部分空間の同定 |
| II・行列 | Axler7.29/7.39 | 実対称正定値行列、正平方根の存在一意性 | 単位行列近傍での逆平方根の収束評価、Gram行列から基底を連続に選ぶ適用 |
| II・比較・派生結果 | Bates Thm2、Kuwae–Shioya2.6、Kroshnin–Stepanov–Trevisan5.4/Rem5.5、Schoenberg§3、Ishiki関連各定理 | 元の幾何条件、compact convergence、GW4と正スペクトルgap、条件付き負性、各次元・位相条件 | これらを本稿の距離kernelの一様近似・局所模型へ一括置換しない。比較紹介は入力不要。個別派生結果のみ必要に応じて使用 |
| III・同変超空間 | Antonyan2003 Prop3.1＋2006訂正 | コンパクト群、連続作用、非空連結・局所連続体連結・距離化可能、Vietoris位相 | Banach模型の仮定、誘導作用の連続性と位相一致 |
| III・軌道AR | Antonyan1990 Thm8/Cor1 | コンパクト群の可算基、距離化可能G-AR | 実際の群の可算基、Banach模型のG-AR、所要商との同定 |
| III・軌道距離 | Palais4.3.4の証明p.319、Antonyan2020 p.4式(2.1) | 等長作用と閉軌道。一般群についてのこの部分のみ | コンパクト群による軌道閉性とinf=min。PalaisのLie群定理全体を仮定しない |
| III・ANRからAR | Hanner1951 7.2(b)、Hanner1952 13.4/12.3、Dugundji12.1 | 固定したcompatible metricで任意εの小さいhomotopy、可分ANRの範囲、全距離化可能域への移行、非空可縮ANE | 近似・実現写像・小さいhomotopyの構成と連続性。可分域の結論から無断で一般域へ移らない |
| IV・積対応 | Ishiki2022Branching Prop5.3の証明 | max積と同じラベルを組にする対応。原定理自体はgeodesicの文脈 | distの差≤max(元の差,尺度差×因子の直径)、歪み/2、尺度のLipschitz性から所要の非拡大性、離散性の構成 |
| IV・Hilbert認識 | Toruńczyk1981 p.248(i)＋1985§C | 非空完備可分metric AR、全開被覆、N×Qからの写像の被覆近接近似、像族がdiscrete | 本稿のAR、離散近似族、全ての量化条件。locally finiteとdiscreteを混同しない |
| IV・付随結論 | Kadets、Uspenskij、Ishikiの非可分Urysohn等 | 元の無限次元・可分性またはrange set等の条件 | 本稿で扱う空間・位相の同定。本文で紹介だけの結果を主定理の入力に含めない |

Peter–Weyl、Larrieu、Leinster–Roff、Shibahara、Yujiや諸コンパクト化・埋込・coarse結果などの比較紹介は、紹介しただけではLeanの依存を増やさない。全引用位置はREGISTER.jsonに残す。各部を実装するときは、実際に必要な命題だけを宣言し、ソース版・locator・型・仮定充足の証明を対応させる。

mathlibでの実装可否を今回網羅検索したわけではない。既存実装以外の表の項目は入力候補であり、利用可能なLean定理名や入力型が確定したという意味ではない。

## 共有補題の実装境界（2026-09-23）

`lem:correspondence-embedding`、`lem:pseudometric-comparison`のQ1–Q4、
`lem:scaling-contraction`はmathlibから証明し、引用定理を追加の仮定にしていない。
近似gluingと最適GH couplingから対応の評価を導出した。
`cor:uniform-separated-sets`は既存の`GHCommonEmbeddingInput.{0}`のみを使用し、
小さいモデルを介して任意universeの列へ適用する。
[共有補題記録](../SHARED.md)を参照。既存引用原典の内容を今回再監査したという意味ではない。

Part IIの作用素基礎は`DistanceKernelSpectralInput`としてMaria–Oudot–Solomon命題12・13のcompact/self-adjoint部分を入力化した。積分公式・定義の一致・二つの評価・連続代表元はLeanで証明。[PART-II.md](../PART-II.md)参照。

Part II cutoff update (2026-09-25): `CompactEigenvalueFinitenessInput` isolates only the general finite-away-from-zero eigenvalue consequence of Muscat 14.19/15.22 in the real self-adjoint case. Its real-case adaptation is documented in EXTERNAL-INPUTS.md. The L²/continuous-cutoff equivalence, finite sum, and dimension transfer are proved internally; complexified spectrum avoidance and simultaneous cutoff selection are now proved in the real-coordinate model of complexification, using the same input plus mathlib Fredholm.

`CompactCutoffRieszRangeInput` の二円特殊化と正確な仮定を `../EXTERNAL-INPUTS.md` に追加（2026-09-26）。Anselone–Palmer p.429 / §7と既存Muscat14.19の一般compact Riesz像の帰結。入力値は未構成であり、距離核への適用と制限同型はLean側。

`RectangleCircleResolventInput` is the explicitly unconstructed specialization of Muscat Corollary12.18 (pp.307–308) and §14.4/Definition14.23 (p.364). Exact scope and source-image audit are in EXTERNAL-INPUTS.md. All distance-kernel and restriction consequences stay on the Lean side.

`CollectivelyCompactSpectralInclusionInput` isolates only Anselone–Palmer Theorem5.3(a), p.427, for compact subsets of the limit resolvent. Exact assumptions and source-image check are in EXTERNAL-INPUTS.md. Selected-kernel convergence and transfer of ±η are proved internally.

`CutoffProjectionConvergenceInput` specializes Anselone–Palmer Proposition6.3 p.429 to fixed cutoff rectangles. It supplies general strong projection convergence and conditional finite-rank stability; exact scope is in EXTERNAL-INPUTS.md. Selected-kernel application and limit finite dimension are proved internally.

EquivariantHyperspaceARInput and OrbitARInput are now explicit Type-0 proposition parameters. SphereOrbit.absoluteRetract discharges their concrete model/group/quotient hypotheses; source statements and limitations are recorded in EXTERNAL-INPUTS.md. No global axiom was added.

HannerDominationInput and HannerANRCategoryInput now encode the two ANR recognition steps with separate ambient categories. The actual GH-space small domination is proved and applied in HannerDomination.lean. Inputs remain explicit, Type 0 only.

ANRToANEInput (Dugundji12.1) and ContractibleANEToAEInput (Hanner12.3) are explicit general Type-0 inputs. GHAbsoluteRetract applies them to the proved ANR and contraction; AE-to-AR is proved internally.

TorunczykRecognitionInput represents Torunczyk1981 p.248 (i), corrected by Torunczyk1985 Section C p.91. Exact quantifiers, real ℓ² model, Type-0 scope, source hashes and verification boundary are recorded in EXTERNAL-INPUTS.md. The main homeomorphism theorem retains this and every earlier input explicitly.

KadetsHomeomorphismInput is the real ℓ² specialization of Kadets1967 p.53, unnumbered Theorem. Its explicit specialization trust boundary, source hash and Type-0 target scope are recorded in EXTERNAL-INPUTS.md. Composition with the main GH homeomorphism is proved internally; concrete Banach examples remain pending.

## Rouyer generic compacta input (2026-09-27-051558)

`PaperN.PartI.RouyerGenericInput` has exactly two fields: the set of GH points
whose representatives are totally anisometric is residual, and the set whose
representatives are perfect is residual. Source: Rouyer, Generic properties of
compact metric spaces (2011), arXiv:1003.5087v1, Theorems 2 and 4. Original TeX
`references/items/arxiv/1003.5087v1/source/cg100318.tex`, definitions lines
55--69 and statements at lines 489 and 577; SHA-256 `cb0533c697519cf2462e3921ed299c60c3d5b6ded9e4e8e72a8db1f698eea839`.
Local original text reread; prior PDF numbering check is in paperN/SOURCE-CHECKS.md.
No fresh PDF-image or source-proof audit is asserted here.
`TotallyAnisometric` compares unordered pairs of distinct points; `PerfectSpace`
means no isolated points on the whole metric carrier. Generic means residual,
not merely dense. GH completeness supplies the Baire implication internally.
The source input has no declared inhabitant and is not a global axiom.
Infinite perfect carriers, rigidity, density of rigid points, conjugacy metric
invariance and pointwise discontinuity are proved internally. The source input
does not assume the desired discontinuity conclusion.

## Curtis–Schori nonempty hyperspace input

`PaperN.PartIII.CurtisSchoriHyperspaceInput.{u}`: for every compact connected
locally connected metric X : Type u with at least two points, NonemptyCompacts X
is homeomorphic to the product-topology Hilbert cube ℕ → Icc (0:ℝ) 1.
Source: D. W. Curtis and R. M. Schori, Hyperspaces of Peano continua are Hilbert
cubes (1978), Theorem 3.2, printed p.21 / PDF page 2. PDF page 1 defines 2^X as
all nonempty closed subsets, not merely subcontinua. In compact metric spaces
closed = compact, proved by peano_closed_iff_compact; peano_hyperspace_dist
checks the actual Hausdorff metric. Fresh visual reading of PDF pages 1 and 2
confirmed the source statement and conventions. Original /Users/yoshitoishiki/Desktop/ghref/16.pdf
SHA-256 cc5f11183768e0a39c8fe1e78f95f4dd940d86797fe1eb800b71995110990311.
The input has no inhabitant or global instance. peano_hyperspace_homeomorphic_cube
is its direct application, not a Lean proof of the source theorem. This cited
remark does not imply an orbit-space result and introduces no assumption into
the existing main GH-space homeomorphism proof.
