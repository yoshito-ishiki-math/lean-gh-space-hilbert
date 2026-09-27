# 外部定理入力

著者の指示（2026-09-20）により、文献に既にある結果は積極的に明示的な定理引数へ
切り出す。原稿の独自の結論・適用条件・定義の一致は Lean 側で接続する。
このファイルは実装済み入力の台帳であり、入力自体の Lean 証明を主張しない。

全原稿の61文献・140引用箇所は [CITATION-REGISTER.md](CITATION-REGISTER.md) を参照。
[各部の切り出し境界](citation-register/LEAN-BOUNDARIES.md)は未実装の候補も含み、
このファイルの実装済み入力と区別する。

## 現在の主定理の入力

最終主定理の入力は `hv`, `hH`, `hO`, `hD`, `hT` の5個。
Part I の主定理の入力は `hv` の1個。
`GHPMetricInput`, `GHPPolishInput`（Type-0）, `GHPCommonEmbeddingInput` は
それぞれ `ghpMetricInput_proved`, `ghpPolishInput_proved`,
`ghpCommonEmbeddingInput_proved` により内部で証明済みとなった。
以下の出典記録は、過去の入力境界と文献対応も保持している。
これは独立した数学的照合の完了を意味しない。

## Khezeli の GHP 入力

出典：Ali Khezeli, *A Unified Framework for Generalizing the Gromov–Hausdorff Metric*,
[arXiv:1812.03760v5](https://arxiv.org/abs/1812.03760v5), 2023-10-27.
刊行情報は *Probability Surveys* 20 (2023), 837–896。
以下のページは arXiv PDF の印刷ページ番号（PDF ページ番号と一致）である。

| 入力 | 正確な Lean 内容 | 原典 |
|---|---|---|
| `GHPMetricInput` | 既存の `MeasuredGHSpace.distance` の三角不等式と距離ゼロの分離性 | p.13, Theorem 2.6。Example 2.1(iii) と Lemma 2.8 による確率測度の場合への特殊化 |
| `GHPPolishInput h` | `h.metricSpace` に関する完備性と可分性 | p.14, Theorem 2.12。Example 2.1(iii), Lemmas 2.8, 2.13 と各コンパクト空間上の確率測度の完備可分性 |
| `GHPCommonEmbeddingInput` | GHP 距離ゼロへの収束から、一つの共通コンパクト空間・等長埋め込み・Hausdorff 収束・押し出し確率の Prokhorov 収束を得る | p.13, Lemma 2.5 の順方向、Example 2.1(iii) |

p.11 の Example 2.1(iii) は有限測度だけでなく確率測度も明示する。
p.12 の Definition 2.4 は空間全体の同型類を用い、式 (8) は共通コンパクト空間内での
Hausdorff 距離と追加構造の距離の **max** を取る。台だけの商・和規約・有点距離ではない。
Theorem 2.6 の pointwise continuity と Theorem 2.12 の Hausdorff continuity を
落とした一般定理を仮定していない。ここでは、それらを満たす確率測度の特殊化を入力する。
Lemma 2.8 と Lemma 2.13 がその連続性を保証する。

## ghref と版の固定

著者指定の `/Users/yoshitoishiki/Desktop/ghref/manifest.json` と `参考文献一覧.md` を確認した。
番号は今後変わり得るので、文献キー・版・ハッシュを識別子として使う。

- `38.pdf`: `Khezeli2023Framework`。今回内容を確認した文献。
  SHA-256: `e6968a3c5cd9ca118d49dfdbb4d01c7671060a243f4e3b2af56bb0ab64a35e76`。
  リポジトリ内の `references/inbox/ghp-comparison-20260907/khezeli-1812.03760v5.pdf`
  とバイト単位で同じ。原典 pp.11–14 を画像でも確認した。2026-09-22にpp.12–15を再確認し、
  以下の単点定値関手と近似確率の入力を追加した。
- `52.pdf`: `ShioyaMetricMeasure`。所在と manifest のハッシュ一致を確認。
  SHA-256: `71fa8df0d63f5160e9965f13b56259164f014a74b1014559f142f26c45e97c23`。
  今回は新しい入力として採用していない。弱収束との橋渡しは既存 mathlib の証明を使う。
- `57.pdf`: `Valov2009`。所在と manifest のハッシュ一致を確認。
  SHA-256: `a0e85b826148a74883f5ebbc29fa0ae8656f07bbb4b6e3883d9b99a946bbffdf`。
  Valov の入力型・原稿への適用は下記の後続チェックポイントで実装済み。
  今回の追加作業ではValov原典の新しい内容を採用していない。

PDF・元の文献フォルダは変更していない。画像とテキストの作業コピーは無視対象の
`references/` 内に置く。版指定のある原典の代わりに一覧だけを証拠としない。

## Lean 側で証明した接続

- `GHPMetricInput.metricSpace`: 入力の二性質と既証明の自己距離ゼロ・対称性を組み合わせ、
  既存の max-infimum を距離として使う `MetricSpace` を作る。
- `ghpPolish_spec h hp`: 完備可分な距離空間として使えることをまとめ、第二可算性を導く。
- `ghpForgetLipschitz_spec h`: 既証明の GH ≤ GHP から忘却写像の 1-Lipschitz 性を導く。
- `invariantProjectionContinuousSurjective_spec h`: 不変全台部分空間への制限は連続全射。
  開性はここに含めない。
- `commonMeasuredEmbedding_spec hc`: Prokhorov 収束を既証明の弱収束との同値で変換し、
  原稿 `lem:common-measured-embedding` の結論を得る。
- `commonMeasuredEmbedding_of_tendsto hm hc`: 同じ結果を商上の GHP 収束から使える形にする。
- `MeasuredGHSpace.continuous_minimumMass hm hc`: 最小球質量のGHP連続性。
- `fullSupportGDelta_spec hm hc`: 全carrier上で全台な確率を持つGHP類のGδ性。
  上の二宣言はGHPPolishInputや新しい仮定を必要としない。
- `invariantGDelta_spec hm hc`, `invariantFullSupportGDelta_spec hm hc`: 不変性と不変全台性のGδ性。
  Prokhorov距離の等長埋め込み不変性はLean内で証明し、引用入力を追加しない。
- `invariantMeasuredPolish_spec hm hp hc`: 元の不変全台部分空間のPolish性。
  `hp : GHPPolishInput hm`も使用する。Gδ部分空間のPolish性はLean内で証明した。

入力の定義と出力の命題は `GHPMetricInput.lean`, `CommonRealization.lean`,
`GHPExternalStatements.lean`、接続の証明は `GHPExternal.lean` に分かれている。
`CheckGHPExternal.lean` は入力と定理型を表示し、公理依存も検査する。

## 証拠と残る境界

入力には **Lean で証明した値を与えていない**。検証されるのは入力からの含意である。
`#print axioms` が標準三公理だけでも、引数で渡した外部定理が Lean 内で証明済みという
意味にはならない。必ず定理の型とこの入力台帳を併読する。

グローバルな GHP 距離空間インスタンスは登録しない。
利用箇所で `letI := h.metricSpace` を置くので、どの入力に依存するかが追跡できる。
原稿の測度選択、等長写像の極限、G_delta 議論、開射影などをこの入力に含めていない。

現在の形式化は universe ごとの商と同じ universe の共通空間を使う。
`smallMeasuredClass`と`measuredUniverseIsometry`により異なるuniverseの商を小さいモデルへ同定済み。元のmax-infimum距離を保存することも証明した。
今回の入力はその形式化された商と距離に直接述べており、別の距離や位相を仮定していない。

## Valov の確率右逆入力（Polish 特殊化）

`ValovProbabilityInput f` は `f : C(X,Y)`、両空間が Polish かつ Borel のとき、
`IsOpenMap f` と `Function.Surjective f` から、弱位相の確率空間間の
`probabilityPushforward f` が連続右逆を持つことを入力する。入力の値は実装していない。
原典は V. Valov, *Probability measures and Milyutin maps between metric spaces*,
arXiv:0801.1721v2, Theorem 1.1 と直後の右逆についての段落（PDF p.2）。
引用台帳の `Valov2009` と同一原典で、キーの年は版・刊行年を代替しない。

- TeX `references/items/arxiv/0801.1721v2/source/arxiv-source.tex`, lines 141–202。
  SHA-256 `c136ddb928f8db7862518ad442f1435c654422e81e8ef26c7f3bb3888efb8128`。
- ghref `57.pdf`, SHA-256 `a0e85b826148a74883f5ebbc29fa0ae8656f07bbb4b6e3883d9b99a946bbffdf`。
- 今回は原TeXの規約・定理・右逆の帰結を再読し、両ハッシュを再検査した。
  画像確認の履歴は全体引用台帳に従い、今回の新規画像検証とはしない。

原典は全ての完全距離化可能空間を対象とするが、今回の型はPolish空間に限定する。
この範囲なら全Borel確率がRadonであり、`probability_innerRegular_polish` により
コンパクト集合による内正則性をmathlibから証明できる。コンパクト台は仮定しない。
弱位相はmathlibの有界連続試験関数によるもの。原典のsoftness全体を形式化する代わりに、
必要な連続右逆の帰結を明示的に入力した。

`valovSelection_spec` はこの右逆と連続Dirac写像を合成する。
`fiberLawSelection_spec` は押し出しがDiracであることから、ファイバーの質量1と
台の包含を導く。これはファイバー内での全台性や群不変性を主張しない。
実際の不変GHP部分空間のPolish性・開射影は入力へ隠さず、Leanで証明した条件を適用する。
`InvariantValovInput hm hp hc` は同じ入力型の実際の射影への特殊化であり、
`invariantFiberLawSelection_spec` がその適用結果。carrierへ運んだ平均の自然性は `naturalInvariantAssignment_spec` へ接続した。
変動carrierでの連続性M3は外部入力に含めず、下記で既存入力から証明した。

## 持ち上げ補題に用いるKhezeli入力（2026-09-22）

`LiftInputs.lean` に次を追加した。入力の値は作らず、引数としてのみ使用する。

| 入力 | 正確な内容 | 原典・照合 |
|---|---|---|
| `GHCommonEmbeddingInput` | 通常のGH収束列と指定された極限を同じコンパクト空間へ等長埋め込みし、全像がHausdorff収束する | v5 p.13 Lemma 2.5、p.15 Example 2.19。単点定値関手では式(8)の追加構造の距離が0で、距離は通常のGHとなる |
| `ProbabilityApproximationInput` | 共通コンパクト空間での全carrierのHausdorff収束から、指定された極限確率へProkhorov収束する通常の確率列を得る | v5 p.11 Example 2.1(iii)、p.14 Lemma 2.13、Remarks 2.14(ii)/2.15。確率を明示し、質量保存・極限確率の任意性を保持 |

`ghref/38.pdf` の上記SHA-256を再確認。既存抽出テキストとpp.12–15の画像を照合した。
p.14の近接点の写像をLeanで構成したとは主張しない。ここで使うのは定理の確率測度への
特殊化と、明記された逐次近似の帰結であり、全台・不変な近似を引用してはいない。
共通GH入力は収束版である。Cauchy列版への接続は後の`commonGHCauchyEmbedding_spec`で、mathlibのGH完備性とこの入力から証明した。原稿のgluing証明を編集せず、形式化側で
同じ収束版を得る別の文献経路を使う。

`invariantLifts_spec hm hg ha` と `openInvariantProjection_spec hm hg ha` は
この二入力と既存GHP距離入力だけに依存する条件付き証明。
GHPPolishInput・GHPCommonEmbeddingInput・Valov入力はこの二宣言には不要。
混合による全台化、Haar平均後の弱収束、GHP infimumによる収束、列の持ち上げからの
開性は全てLean側で証明した。

## ファイバー移送の接続（2026-09-22）

ファイバーの確率の一意性、固定carrierでの連続性、制限・移送・平均、自然性は
Lean内で証明した。新しい引用入力はない。`naturalInvariantAssignment_spec` は
前回と同じ6入力からのM1・M2の条件付き接続で、M3は含めない。

`limitSupport_spec` と変動carrierの `eq:fiber-pullbacks` を追加した。前者は引用入力不要、後者は既存のGHP距離入力だけを使う。M3の平均の収束は入力に含めない。下記のfamily構成まで証明し、既存選択への接続も下記で証明した。

`diracProduct_spec`は原稿のDirac積補題をmathlibから証明。Tietzeによる閉定義域への制限・連続移送・平均の一般収束補題も外部入力不要。`familyFiberAverage_tendsto`は既存hm/hpのみを使い、hpからはseparabilityだけを使用する。同じ選択のM3への同定も下記で実装。

`invariantAssignment_spec` は新規入力を加えず、同じ既存六入力からM1・M2・M3を同時に満たす割当をType 0のモデルで証明する。M3の接続自体はhm・hpと既存Valov法則の連続性を使用する。D(X) API・universe橋渡しは後の完了記録で実装した。

`ghpRetraction_spec` は同じ六入力からType 0モデルのretractの系を証明する。sectionの連続性の接続はhm・hp・hgと既存選択のM3を使用し、新規の外部入力やAR性を追加しない。

`fixedTopologyAssignment_spec`、`ghpRetraction_universe`は同じ六つのType 0入力から任意universeの結論を証明する。`GHPMetricInput.universe`と`ghpPolish_universe`は距離保存同型による帰結であり、新しい引用入力ではない。平均作用素の注記にも新しい入力は不要。

## Part II: 距離核のコンパクト性・自己共役性

更新：`PaperN.PartII.distanceKernelSpectralInput_proved`により、この入力の値をLean内で証明した。
新しい主定理 `ghSpace_homeomorphic_hilbert_main` は `hk` を外部から受け取らない。
以下の出典と未構成という記述は導入当時の履歴であり、現在の境界はこの更新を優先する。

`PaperN.PartII.DistanceKernelSpectralInput.{u}`は、非空compact距離空間XとBorel確率測度μに対し、
実装済み`distanceOperator μ`がcompactかつself-adjointであるという命題。
出典は Clément Maria, Steve Oudot, Justin Solomon,
*Intrinsic Topological Transforms via the Distance Kernel Embedding*, SoCG 2020,
DOI 10.4230/LIPIcs.SoCG.2020.56, Definition 11 and Propositions 12–13, pp.56:6–56:7。
`/Users/yoshitoishiki/Desktop/ghref/43.pdf`、SHA-256
`74e84fbf3746f8a1c5901f691cffd0c11d07ac8de3d895d0d6a10c651123a3da`。
2026-09-24にhashと原文を再確認。原典の有限Radon測度をcompact距離空間上の確率測度へ特殊化。
単純固有値、固有値の順序、spectral coordinatesのinjectivityなどは仮定しない。
`distanceValue_integral`と`distanceOperator_ae`で原典の積分作用素との一致をLeanで証明。
一様評価・Lipschitz評価・連続代表元はLean側の証明であり、この入力には含まない。
入力のinhabitantは証明していない。グローバルなaxiomは導入しない。

## Part II: 閾値より大きい固有値の有限性

更新：`PaperN.PartII.compactEigenvalueFinitenessInput_proved` が全宇宙でこの入力を証明する。
現在の主定理は `hf` を外部から受け取らない。以下の未構成という記述は導入当時の履歴。

`CompactEigenvalueFinitenessInput.{u}`は、任意の実Hilbert空間上のcompact self-adjoint作用素Tとη>0に対し、`{a : ℝ | η < |a| ∧ HasEigenvalue T a}`が有限である、という一般の引用入力。
Joseph Muscat, *Functional Analysis* (2024), Theorem 14.19, printed pp.361–362 (PDF pp.360–361), and Theorem 15.22, printed p.400 (PDF p.399)の実自己共役の場合の帰結。
`/Users/yoshitoishiki/Desktop/ghref/45.pdf`、SHA-256 `c311b4bb64d812297e36d3b15168fbb2b05900af68aac1ed8f27c4d625a5ff98`。2026-09-25にhashと原文を再確認。
原典の14.19は複素スペクトルの定理であり、この入力はその文面の逐語訳ではない。14.19の閾値以上の異なる固有値を用いるコンパクト性の証明、または15.22の直交固有ベクトルの像の距離を用いる証明は、実自己共役作用素にもそのまま適用できる。後者はseparabilityを要しない。この実版への適用は同一agentによる数学的照合で、Lean内の証明ではない。
入力は固有値集合の有限性だけ。個々の非零固有空間の有限次元性はmathlib、有限和・C(X)との線形同型・次元移送・非零性から正次元性への接続はLean内で証明する。引用入力のinhabitantは未構成であり、グローバルaxiomは置かない。複素化スペクトルは `ComplexifiedSpectrum.lean` のH×H実座標モデルで定義。±η回避はこの有限性、mathlibのFredholm alternative、実逆作用素を両座標へ作用させるLean内の構成から導く。回避そのものを新しい引用入力にはしない。

## 複素カットオフへの既存入力の移送（2026-09-26）

`ComplexCutoffFinite.lean` は既存 `CompactEigenvalueFinitenessInput` を同じunderlying spaceの実スカラー制限に適用する。複素対称作用素の固有値が実数であること、実固有値への対応、複素固有値集合の有限性への移送はLean内で証明した。複素版の引用入力を新設していない。カットオフ代数和の有限次元性、閉包との一致、二円積分の有限次元像の同定はこの既存入力に条件付き。個別の非零固有空間の有限次元性はmathlibを使用する。先行する二円積分と閉固有空間への直交射影の一致には、この入力は不要。

## Part II: compact Riesz像の二円特殊化（2026-09-26）

`CompactCutoffRieszRangeInput.{u}` は複素Banach空間上のcompact作用素Uについて、η>0、η<B、スペクトルが実軸上でノルム<B、±ηがレゾルベント集合にあるとき、実装済み `cutoffCircleOperator U η B` の像が |λ|>η の `maxGenEigenspace` の代数和に一致することを入力する。入力値は未構成。グローバルaxiom・instanceはない。

原典は P. M. Anselone and T. W. Palmer, Spectral analysis of collectively compact, strongly convergent operator sequences (1968), p.429のスペクトル部分空間の記述と§7の EX=ker P(T)。単一の孤立固有値の記述を、compactスペクトルの零から離れた有限部分に足し合わせる標準的帰結として特殊化する。有限性は既存台帳のMuscat Theorem 14.19による。二円は正向き、互いに交わらず0を除外し、選択点の巻数1、その他0となる。これは原典に距離核の定理があるという主張ではなく、一般Riesz定理の特殊化である。

今回ghref/1.pdfのSHA-256 `a66d73fdef8edbaf25dbf6a8ae7cef64b7d84bdf036ce73cf17039e830be69aa` とghref/45.pdfのSHA-256 `c311b4bb64d812297e36d3b15168fbb2b05900af68aac1ed8f27c4d625a5ff98` を再確認し、Anselone–Palmer p.429は `references/derived/pages/riesz-finite-spectral-set-20260924/anselone-palmer-riesz-p429.png` で画像確認した。Muscatの有限性の原典照合は既存記録を再利用。入力の特殊化・有限和への数学的照合は同一agent、独立確認ではない。

入力には周囲距離作用素、制限写像、一般化固有空間の安定化、実関数保存性、矩形との一致、変動空間での収束は含まれない。`ambient_cutoffCircle_range` と像上の制限同型、冪等性がこの入力に条件付き。冪等性自体は像の同定と既証明の固有ベクトル作用からLeanで導く。

## Rectangle/circle contour independence (2026-09-26)

`RectangleCircleResolventInput.{u}` quantifies over arbitrary complex Banach spaces
and bounded operators with real spectrum. For l<r, h>0 and resolvent endpoints l,r,
it equates the implemented positively oriented rectangle integral with the
implemented circle integral centered at (l+r)/2 of radius (r-l)/2. No compactness,
distance kernel, real preservation, restriction map or convergence is in the input.
Its inhabitant is not constructed; there is no global axiom/instance.

Source: Joseph Muscat, Functional Analysis (2024), Corollary 12.18 and its proof,
printed pp.307–308, and §14.4 introductory paragraph / Definition 14.23, printed
p.364. The cited general statement is Cauchy deformation invariance for analytic
Banach-valued integrands, applied to the resolvent. The displayed Lean equality
is our geometric specialization, not a verbatim theorem in the book. Both curves
meet the real axis only at l,r and have winding number one on (l,r), zero on the
remaining real spectrum. Both avoid the spectrum. Resolvent analyticity and
Cauchy's deformation theorem therefore identify their operator-norm integrals.
The rectangle is lower-right-upper-left, and the circle is counterclockwise;
both normalizations are 1/(2πi). This applies also when selected spectrum is empty.

Source hash: ghref/45.pdf SHA-256
`c311b4bb64d812297e36d3b15168fbb2b05900af68aac1ed8f27c4d625a5ff98`.
Text and images reread: PDF pages 309,310,363, rendered under
`references/derived/pages/contour-comparison-20260926/`.
Alignment by Codex, same agent, non-independent. The geometry/specialization is
mathematically audited; general contour independence is not proved in Lean here.
`cutoffContour_eq_circle` applies the input twice. The ambient spectrum bound,
endpoint transfer and projection-restriction consequences are proved in Lean.

## Collectively compact spectral inclusion (2026-09-26)

`CollectivelyCompactSpectralInclusionInput` is Anselone–Palmer (1968), Theorem
5.3(a), printed p.427, specialized to a compact subset A of the limit resolvent.
For arbitrary complex Banach E and bounded U_n,U, it requires strong convergence
and one compact set containing all (U_n-U)x for ||x||≤1. It returns eventual
A⊆resolvent(U_n). It assumes no distance kernel, selected measure, self-adjointness,
finite rank or projection convergence. No inhabitant/global axiom is asserted.

Source proof: take Ω=ℂ\A, an open neighborhood of spectrum(U); Theorem5.3(a)
gives spectrum(U_n)⊆Ω eventually. Its original complement in the extended plane
intersects ℂ in exactly A. Compact containment of unit-ball images is the usual
collective compactness condition, by scaling bounded sets. Text and p.427 image
were reread at references/inbox/owner-62/anselone-6.txt and anselone-6.png.
The source /Users/yoshitoishiki/Desktop/ghref/1.pdf hash was rechecked:
`a66d73fdef8edbaf25dbf6a8ae7cef64b7d84bdf036ce73cf17039e830be69aa`.
Same-agent, non-independent source/specialization audit. The new Lean theorems
supply the analytic hypotheses from the selected distance operators, take
A={η,-η}, and use nonzero spectral correspondence to return to the original L²
operators. These applications are not part of the quoted input.

## Fixed-contour spectral projections (2026-09-26)

`CutoffProjectionConvergenceInput` specializes Anselone–Palmer (1968), Proposition
6.3, p.429, to the implemented fixed two-rectangle contour. It requires a strongly
convergent complex Banach operator sequence, compact containment of the unit-ball
images of its differences, a real limit spectrum bounded by D≥0, η>0 and limit
resolvent endpoints ±η. It gives strong convergence of cutoffContourOperator and,
if the limit projection range is finite-dimensional, eventual finite-dimensional
ranges of the same complex finrank. No distance kernels, measures, Hausdorff
convergence, real cutoff dimension or real preservation are in this input.
The fixed outer endpoint is D+η+1 and height is 1. Limit spectral bounds and
endpoint exclusions put all edges in the limit resolvent; both components are
positively oriented and disjoint. Proposition6.3 applies to their finite union.
The finite-dimensional implication is a specialization of its dimension equality.
No global axiom/instance/inhabitant is asserted.

The p.429 text and image were reread at references/inbox/owner-62/anselone-8.txt
and anselone-8.png. Source ghref/1.pdf is the same hash checked at the immediately
preceding checkpoint: a66d73fdef8edbaf25dbf6a8ae7cef64b7d84bdf036ce73cf17039e830be69aa.
Same-agent, non-independent source and specialization audit. Strong convergence
is on each fixed vector, not operator-norm convergence. The integrals for finitely
many early indices need not be Riesz projections; their total Lean definitions
do not affect limits or eventual conclusions. Concrete limit finite dimension
and selected-measure hypotheses are proved outside the input.

## Equivariant hyperspace and orbit AR inputs

`EquivariantHyperspaceARInput` is the general metric-space specialization of
Antonyan 2003 Proposition 3.1 (pp.3385–3386), with the 2006 correction. It
requires a compact Hausdorff topological group, continuous action, a nonempty
connected metric space and an open basis of continuum-connected sets. The
hyperspace action must equal setwise image. `NonemptyCompacts` uses the existing
mathlib Vietoris-compatible Hausdorff topology (Topology/MetricSpace/Closeds.lean,
NonemptyCompacts.instEMetricSpace, and Topology/UniformSpace/Closeds.lean).
The 2006 correction changes the G-nerve construction, not Proposition 3.1.

`OrbitARInput` is the H=G specialization of Antonyan 1990 Theorem 8 and Corollary 1
(pp.317–320; PDF13–16). It requires a compact Hausdorff topological group with a
countable basis and a metrizable G-AR. Its conclusion is the metrizable AR
property of any quotient presentation whose fibers are exactly the orbits.
This is presentation-independent because quotient maps with identical fibers
have canonically homeomorphic targets; it does not assume an arbitrary map's
target is an orbit space. Both inputs and their ambient AR test spaces are
explicitly Type 0. Larger-universe AR conclusions are not supplied by them.

These are proposition parameters, not global axioms or proved Lean citations.
The concrete model, group and orbit hypotheses are proved in SphereOrbitAR.lean.
Same-agent source alignment uses the existing citation audit plus rereading
Proposition 3.1, Theorem 8/Corollary 1 and the correction in the saved text.
Live source hashes were rechecked against the register. No independent review.

- Antonyan1990: /Users/yoshitoishiki/Desktop/ghref/2.pdf; SHA256 1ebecb37690fb6f517224db5f58dff2d4719b5ffd65da058fa594b0123a88215
- Antonyan2003West: /Users/yoshitoishiki/Desktop/ghref/3.pdf; SHA256 337fcf46c1f5721a18c47729ac17f6fbcf948ed2744879aac46218b769660f21
- Antonyan2006Correction: /Users/yoshitoishiki/Desktop/ghref/4.pdf; SHA256 663b25bd4dfef7943d36ffc5451cb260d1b68bb7e25543ee1ed2864d6d6713b3

## Hanner domination and ambient-category inputs

`HannerDominationInput` specializes Hanner 1951 Theorem 7.2(b) to a fixed
compatible metric on a separable metric space. For every positive constant,
it assumes a separable metrizable ANR and continuous factorization maps with
a jointly continuous identity-to-composite homotopy whose tracks have diameter
less than that constant. The auxiliary ANR is required for all metrizable
ambient spaces, a stronger hypothesis than the separable category in the source.
Its conclusion is ANR for separable metrizable ambient spaces.
`HannerANRCategoryInput` is Hanner 1952 Theorem 13.4: for a separable target,
ANR in separable metrizable ambient spaces implies ANR in all metrizable ones.
Both are general Type-0 proposition parameters, not global axioms or proofs of
the cited theorems. Same-agent non-independent alignment used the existing
citation audit and reread saved source text: 1951 pp.404–405 (PDF16–17),
1952 Theorem13.4 (PDF19). Live PDF hashes were checked against saved records.
The definitions quantify closed embeddings and actual continuous retractions
on open neighbourhoods; no separability restriction leaks into the full category.
- Hanner1951: /Users/yoshitoishiki/Desktop/ghref/21.pdf; SHA256 7318eae048438431b20d872f1bcd4d8f770a5e2cd26f84516de750bd6a8b0bc3
- Hanner1952: /Users/yoshitoishiki/Desktop/ghref/22.pdf; SHA256 42ea0e766b9e9582edfa204f8cadcdcdf698f0d7849760b7e4e3082f20a997ab

## General extension inputs for Part III

`ANRToANEInput` is the ANR-to-neighbourhood-extension implication of
Dugundji 1958 Theorem 12.1 (PDF12), with the source's extension-based terminology
translated to IsAbsoluteNeighborhoodExtensor. `ContractibleANEToAEInput` is
Hanner 1952 Theorem 12.3 (PDF17–18), restricted to metrizable ambient spaces,
which are normal. It assumes an explicitly nonempty contractible ANE.
These are general Type-0 proposition parameters without global inhabitants.
Same-agent non-independent alignment reused the existing citation audit and
reread saved source text; live PDF hashes were checked. The reverse directions
AE-to-AR and ANE-to-ANR are proved directly in AbsoluteExtensor.lean and need
no citation input. No AR-to-AE equivalence beyond the stated direction is
silently assumed. GH contraction is the existing Shared.ghSpace_contractible.
- Dugundji1958: /Users/yoshitoishiki/Desktop/ghref/18.pdf; SHA256 201eaa84f6b43690c145f2fe47656943f92d5e5ed955404f5c0d88ccff4399d4
- Hanner1952: /Users/yoshitoishiki/Desktop/ghref/22.pdf; SHA256 42ea0e766b9e9582edfa204f8cadcdcdf698f0d7849760b7e4e3082f20a997ab

## Torunczyk recognition input

`PaperN.PartIV.TorunczykRecognitionInput` is the general equivalence for a
nonempty complete separable metric Type-0 AR between homeomorphism to the real
square-summable sequence space `lp (fun _ : ℕ ↦ ℝ) 2` and
HasHilbertCubeDiscreteApproximation. It is a proposition parameter, not a global
axiom and not a constructed proof of Torunczyk's theorem.
Sources: Torunczyk 1981, Characterizing Hilbert space topology, p.248 (i)
(PDF page 2), with Torunczyk 1985, A correction of two papers, Section C, p.91
(PDF page 2). The latter repairs the recognition proof; no altered condition
is introduced here. Existing source-image checks are recorded in
paperN/reviews/citation-audit-20260913-165458/REPORT.md. This checkpoint reread
the page-delimited extracted text and verified original PDF hashes, without
claiming a fresh source-image or independent proof audit.
The source's countably infinite discrete index is instantiated by ℕ; reindexing
does not affect the condition. Q is the product [0,1]^ℕ. Closeness quantifies over
all open covers, and discreteness applies at all ambient points. The source's
AR category is represented by the established IsAbsoluteRetract.{0,0}; this
is explicitly a Type-0 formal input, with no universe-polymorphic claim.
GH completeness, separability and nonemptiness are mathlib instances; the AR
premise and discrete approximation are proved from their explicit earlier
inputs. The final theorem lists all 17 input hypotheses, rather than treating
any as an implicit instance or claiming the citation itself was proved in Lean.

- 1981 PDF: /Users/yoshitoishiki/Desktop/ghref/53.pdf; SHA256 3594221c57ba6438e10ad7be28e68f8bbaf3cab306c5904ebc4f666a4cae31a0
- 1985 PDF: /Users/yoshitoishiki/Desktop/ghref/54.pdf; SHA256 783f52de2e8f432aa2794be5419139ce48bb02e7cc1db8581b373cec12060f08

## Kadets Banach-space specialization

`PaperN.PartIV.KadetsHomeomorphismInput` supplies a homeomorphism from the actual
real sequence space `lp (fun _ : ℕ ↦ ℝ) 2` to every complete separable real normed
Type-0 space E with `¬ FiniteDimensional ℝ E`. Source: M. I. Kadets, Proof of the
topological equivalence of all separable infinite-dimensional Banach spaces,
1967, p.53 / PDF page 1, unnumbered Theorem. The published statement compares
any two such Banach spaces. Fixing the first to real ℓ² uses its standard
completeness, separability and infinite dimensionality. This checkpoint packages
that specialization as the explicit citation input; it does not claim separate
Lean proofs of the latter two facts. This is neither a linear equivalence nor
an isometry, and the formal target remains Type 0.

Local source: /Users/yoshitoishiki/Desktop/ghref/36.pdf; SHA256
`a744f2fca66d40151c903b94689209f969e098692b0d673c5cc4b0fcf63532f9`.
The checkpoint verified the original hash and reread the page-delimited text,
using the existing citation audit at paperN/reviews/citation-audit-20260913-165458/REPORT.md.
No fresh source-image or independent source-proof audit is claimed. The input
has no constructed Lean inhabitant or global axiom. The GH consequence is
proved by homeomorphism composition. Concrete C([0,1]) and ℓᵖ examples remain
pending formal instance verification and specialization.

Subsequent formal discharge of the ℓ² specialization facts:
`SequenceBanachSpaces.realHilbert_separable` and
`SequenceBanachSpaces.realHilbert_not_finiteDimensional` (declarations in the
`PaperN.PartIV` namespace) now prove separability and infinite dimension of the
actual RealHilbertSpace model. Completeness is mathlib `lp.completeSpace`.
Thus these facts need no longer be trusted only as informal specialization facts.
Kadets itself remains the explicitly unconstructed cited input. The finite-p
ℓᵖ examples are now instantiated; C([0,1]) remains pending.

The C([0,1],ℝ) example is now instantiated by `ghSpace_homeomorphic_intervalFunctions`:
`ContinuousBanachSpace.lean` proves infinite dimension via polynomial restriction
and verifies the standard completeness and separability instances. Both named
Banach examples have thus been discharged without further citation inputs.

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

### Hanner category input discharged internally

`hannerANRCategoryInput_proved` inhabits the exact registered
`HannerANRCategoryInput`. A countable Tietze factor retains the target as a
closed embedding into a separable metric space; the neighbourhood retraction
pulls back to an open neighbourhood of the original target. Empty targets
use the empty neighbourhood. The stronger `allUniverses` theorem admits
arbitrary ambient universes. No new external input is introduced.

`ghSpace_homeomorphic_hilbert_main` now supplies this proof internally and
has **16 remaining external inputs**. Historical 17/18/19-input checkpoints
remain historical. Existing citations are not asserted to be Lean proofs.

Evidence: `verification/hanner-category-2026-09-27-065659/`.

### Contractible ANE-to-AE input discharged internally

`contractibleANEToAEInput_proved` inhabits the exact registered input.
`IsAbsoluteNeighborhoodExtensor.of_contractible` works in any ambient universe.
For a closed extension domain A inside the ANE neighbourhood U, normality gives
an open V with A contained in V and closure V contained in U. Urysohn supplies
a parameter zero on A and one outside V. Composing the local extension with
the contraction gives the original map on A and the contraction endpoint
outside closure V. Continuity follows on U and its complementary boundary
region, which together cover the ambient. No uniformity of the contraction
at infinity and no compactness of A are assumed.

`ghSpace_homeomorphic_hilbert_main` now supplies this proof internally and
has **15 remaining external inputs**. Prior input counts are historical.
No new external input, global axiom, or independent certification is claimed.

Evidence: `verification/contractible-extensor-2026-09-27-070137/`.

### Probability approximation input discharged internally

`probabilityApproximationInput_proved` inhabits the exact registered input in
any universe. The first suitable point in a dense sequence defines a measurable
map from the limit carrier to each approximating carrier. Its ambient error
is less than the Hausdorff distance plus 1/(n+1). Pushing forward the prescribed
limit probability and using the uniform Prokhorov bound proves the required
convergence. The original embeddings and entire carriers are retained; no
invariance or full-support property is asserted by this input.

`ghSpace_homeomorphic_hilbert_main` now supplies this proof internally and
has **14 remaining external inputs**. No new external input is introduced.

Evidence: `verification/probability-approx-2026-09-27-071057/`.

### GH common embedding input discharged internally

`ghCommonEmbeddingInput_proved` inhabits the exact registered input in every
universe. Optimal couplings are glued along the fixed limit carrier. The metric
inductive limit realizes all distances to that carrier simultaneously. The
sequence of compact images converges in the Hausdorff hyperspace; its range
with its limit is compact, so the union of the corresponding compact subsets
is compact by mathlib's Vietoris theorem. Restricting the isometries to this
union produces the required `CommonRealization` and Hausdorff convergence.
No subsequence is substituted and no measured convergence is asserted.

`ghSpace_homeomorphic_hilbert_main` supplies this proof internally and now has
**13 remaining external inputs**. No new external input is introduced.

Evidence: `verification/gh-common-2026-09-27-071823/`.

### Finite cutoff resolvent proof removes the general spectral input

The active dependency chain now uses internally proved finite-set resolvent
stability at the two cutoff points. The geometric and analytic conclusions of
all downstream theorems are unchanged. `CollectivelyCompactSpectralInclusionInput`
and its historical general wrapper remain available but are not required by
the main proof. The general compact-set theorem has NOT been proved here.

`ghSpace_homeomorphic_hilbert_main` now has **12 remaining external inputs**.
This removes an unnecessary dependency rather than claiming a proof of the
stronger unused statement. The chain uses the compact-uniform convergence,
squared-error and eventual-invertibility proofs recorded in recent checkpoints.

## Compact resolvent inclusion now proved internally

`collectivelyCompactSpectralInclusionInput_proved` inhabits the full compact-set
predicate using `collectivelyCompact_eventually_compact_resolvent_bound`.
Finite subcovers of the common neighbourhoods give one eventual index and
a bound equal to the sum of finitely many nonnegative local bounds. Empty
compact sets are included. Earlier statements that the full predicate has
no inhabitant are superseded by this checkpoint. The active main already
avoided this input, so its remaining external count stays 12.

## Cutoff contour strong convergence proved internally

`collectivelyCompact_cutoffContourOperator_tendsto` proves the entire strong
convergence conjunct of `CutoffProjectionConvergenceInput` with its existing
hypotheses and actual contour definition. The finite-dimensionality and
eventual equal-rank conjunct remains unproved internally. The original
combined input is still exposed, and the main external count remains 12.

## Selected projection convergence input removed

The active `ghSpace_homeomorphic_hilbert_main` has **11 remaining external
inputs**. `hP : CutoffProjectionConvergenceInput` is removed from its entire
downstream chain. `selectedCutoffProjection_rank_proved` supplies complex
rank equality; `selectedCutoff_eventual_real_dimension` transports it to
the real cutoff, and `spectralProjections_spec` uses the internal strong
convergence proof. The retained Riesz-range and rectangle-circle inputs
supply the selected projection identities. The general input predicate
and its legacy wrappers remain, without an asserted inhabitant. Earlier
12-input checkpoints describe historical states.

### Removal of the ambient Riesz-range argument

The active main theorem now declares **10 external inputs**: `hm`, `hp`,
`hc`, `hv`, `hC`, `hH`, `hO`, `hD`, `hE`, and `hT`. The argument
`hR : CompactCutoffRieszRangeInput` has been removed from the ambient
distance-kernel chain through the main theorem. Its required range equality
is supplied by `ambient_cutoffCircle_range_proved`. The general Banach-space
predicate remains defined without an asserted inhabitant. Earlier 11-input
checkpoints are historical. This does not remove the rectangle-circle
comparison input `hC`, and does not establish the unconditional main theorem.

### Rectangle-circle input removed from the active main

The active main now declares **9 external inputs**: `hm`, `hp`, `hc`,
`hv`, `hH`, `hO`, `hD`, `hE`, and `hT`. The hC argument is removed
from the selected distance-kernel chain. The comparison is supplied by
`ambient_cutoffContour_eq_circle_of_bound`, including the larger diameter
of the common ambient space. The general Banach-space predicate and its
generic conditional wrapper remain without an asserted inhabitant. Earlier
10-input checkpoints are historical. The main theorem remains conditional
on these nine inputs; independent alignment review is still pending.

### ANR-to-ANE input removed from the active main

The active main has **8 external inputs**: `hm`, `hp`, `hc`, `hv`, `hH`,
`hO`, `hD`, and `hT`. GH-space neighbourhood extension now follows from
`IsAbsoluteNeighborhoodRetract.isAbsoluteNeighborhoodExtensor_of_separable`.
The hE argument was removed throughout the active downstream chain. The
general nonseparable ANRToANEInput predicate remains defined without an
asserted inhabitant. Earlier nine-input checkpoints are historical. The
main remains conditional, and independent alignment review remains pending.
