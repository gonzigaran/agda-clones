---
layout: default
title : "Clones.Basic module"
date : "2023-10-18"
author: "Gonzalo Zigarán"
---

# Clones: Basic definitions


<pre class="Agda"><a id="140" class="Keyword">module</a> <a id="147" href="Clones.Basic.html" class="Module">Clones.Basic</a> <a id="160" class="Keyword">where</a>

<a id="167" class="Keyword">open</a> <a id="172" class="Keyword">import</a> <a id="179" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>               <a id="208" class="Keyword">using</a> <a id="214" class="Symbol">()</a> <a id="217" class="Keyword">renaming</a> <a id="226" class="Symbol">(</a> <a id="228" href="Agda.Primitive.html#320" class="Primitive">Set</a> <a id="232" class="Symbol">to</a> <a id="235" class="Primitive">Type</a> <a id="240" class="Symbol">)</a>
<a id="242" class="Keyword">open</a> <a id="247" class="Keyword">import</a> <a id="254" href="Level.html" class="Module">Level</a>                        <a id="283" class="Keyword">using</a> <a id="289" class="Symbol">(</a> <a id="291" href="Agda.Primitive.html#804" class="Primitive Operator">_⊔_</a> <a id="295" class="Symbol">;</a> <a id="297" href="Agda.Primitive.html#591" class="Postulate">Level</a> <a id="303" class="Symbol">;</a> <a id="305" href="Agda.Primitive.html#774" class="Primitive">suc</a> <a id="309" class="Symbol">)</a>
<a id="311" class="Keyword">open</a> <a id="316" class="Keyword">import</a> <a id="323" href="Data.Nat.html" class="Module">Data.Nat</a>                     <a id="352" class="Keyword">using</a> <a id="358" class="Symbol">(</a> <a id="360" href="Agda.Builtin.Nat.html#186" class="Datatype">ℕ</a> <a id="362" class="Symbol">)</a>
<a id="364" class="Keyword">open</a> <a id="369" class="Keyword">import</a> <a id="376" href="Data.Fin.html" class="Module">Data.Fin</a>                     <a id="405" class="Keyword">using</a> <a id="411" class="Symbol">(</a> <a id="413" href="Data.Fin.Base.html#1135" class="Datatype">Fin</a> <a id="417" class="Symbol">)</a>
<a id="419" class="Keyword">open</a> <a id="424" class="Keyword">import</a> <a id="431" href="Data.Product.html" class="Module">Data.Product</a>                 <a id="460" class="Keyword">using</a> <a id="466" class="Symbol">(</a> <a id="468" href="Data.Product.html#1176" class="Function Operator">_×_</a> <a id="472" class="Symbol">;</a> <a id="474" href="Data.Product.html#925" class="Function">Σ-syntax</a> <a id="483" class="Symbol">;</a> <a id="485" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">_,_</a> <a id="489" class="Symbol">)</a>
<a id="491" class="Keyword">open</a> <a id="496" class="Keyword">import</a> <a id="503" href="Relation.Unary.html" class="Module">Relation.Unary</a>       <a id="524" class="Keyword">using</a> <a id="530" class="Symbol">(</a> <a id="532" href="Relation.Unary.html#1110" class="Function">Pred</a> <a id="537" class="Symbol">;</a> <a id="539" href="Relation.Unary.html#1532" class="Function Operator">_∈_</a> <a id="543" class="Symbol">)</a>

<a id="546" class="Keyword">private</a> <a id="554" class="Keyword">variable</a> <a id="563" href="Clones.Basic.html#563" class="Generalizable">α</a> <a id="565" href="Clones.Basic.html#565" class="Generalizable">ρ</a> <a id="567" class="Symbol">:</a> <a id="569" href="Agda.Primitive.html#591" class="Postulate">Level</a>

</pre>
## Operaciones y Relaciones

Para un conjunto $A$ y un $n ∈ ℕ$, definimos el conjunto de operaciones $n$-arias, y luego el conjunto de operaciones de aridad finita.

<pre class="Agda">
<a id="756" class="Keyword">open</a> <a id="761" class="Keyword">import</a> <a id="768" href="Overture.html" class="Module">Overture</a>        <a id="784" class="Keyword">using</a> <a id="790" class="Symbol">(</a> <a id="792" href="Overture.Operations.html#1235" class="Function">Op</a> <a id="795" class="Symbol">)</a>
<a id="797" class="Comment">-- Operaciones de aridad finita</a>
<a id="FinOp"></a><a id="829" href="Clones.Basic.html#829" class="Function">FinOp</a> <a id="835" class="Symbol">:</a> <a id="837" class="Symbol">{</a> <a id="839" href="Clones.Basic.html#839" class="Bound">n</a> <a id="841" class="Symbol">:</a> <a id="843" href="Agda.Builtin.Nat.html#186" class="Datatype">ℕ</a> <a id="845" class="Symbol">}</a> <a id="847" class="Symbol">→</a> <a id="849" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="854" href="Clones.Basic.html#563" class="Generalizable">α</a> <a id="856" class="Symbol">→</a> <a id="858" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="863" href="Clones.Basic.html#563" class="Generalizable">α</a>
<a id="865" href="Clones.Basic.html#829" class="Function">FinOp</a> <a id="871" class="Symbol">{</a> <a id="873" class="Argument">n</a> <a id="875" class="Symbol">=</a> <a id="877" href="Clones.Basic.html#877" class="Bound">n</a> <a id="879" class="Symbol">}</a> <a id="881" href="Clones.Basic.html#881" class="Bound">A</a> <a id="883" class="Symbol">=</a> <a id="885" href="Overture.Operations.html#1235" class="Function">Op</a> <a id="888" href="Clones.Basic.html#881" class="Bound">A</a> <a id="890" class="Symbol">(</a><a id="891" href="Data.Fin.Base.html#1135" class="Datatype">Fin</a> <a id="895" href="Clones.Basic.html#877" class="Bound">n</a><a id="896" class="Symbol">)</a>

<a id="FinOps"></a><a id="899" href="Clones.Basic.html#899" class="Function">FinOps</a> <a id="906" class="Symbol">:</a> <a id="908" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="913" href="Clones.Basic.html#563" class="Generalizable">α</a> <a id="915" class="Symbol">→</a> <a id="917" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="922" href="Clones.Basic.html#563" class="Generalizable">α</a>
<a id="924" href="Clones.Basic.html#899" class="Function">FinOps</a> <a id="931" href="Clones.Basic.html#931" class="Bound">A</a> <a id="933" class="Symbol">=</a> <a id="935" href="Data.Product.html#925" class="Function">Σ[</a> <a id="938" href="Clones.Basic.html#938" class="Bound">n</a> <a id="940" href="Data.Product.html#925" class="Function">∈</a> <a id="942" href="Agda.Builtin.Nat.html#186" class="Datatype">ℕ</a> <a id="944" href="Data.Product.html#925" class="Function">]</a> <a id="946" class="Symbol">(</a><a id="947" href="Clones.Basic.html#829" class="Function">FinOp</a> <a id="953" class="Symbol">{</a><a id="954" class="Argument">n</a> <a id="956" class="Symbol">=</a> <a id="958" href="Clones.Basic.html#938" class="Bound">n</a><a id="959" class="Symbol">}</a> <a id="961" href="Clones.Basic.html#931" class="Bound">A</a><a id="962" class="Symbol">)</a>

</pre>
De la misma manera, el conjunto de relaciones con elementos de $A$ de aridad $n$, con $n ∈ ℕ$ fijo, y de relaciones de aridad finita

<pre class="Agda">
<a id="1113" class="Keyword">open</a> <a id="1118" class="Keyword">import</a> <a id="1125" href="Base.Relations.Continuous.html" class="Module">Base.Relations.Continuous</a>    <a id="1154" class="Keyword">using</a> <a id="1160" class="Symbol">(</a> <a id="1162" href="Base.Relations.Continuous.html#4456" class="Function">Rel</a> <a id="1166" class="Symbol">)</a>
<a id="1168" class="Comment">-- Relaciones de aridad finita</a>
<a id="FinRel"></a><a id="1199" href="Clones.Basic.html#1199" class="Function">FinRel</a> <a id="1206" class="Symbol">:</a> <a id="1208" class="Symbol">{</a> <a id="1210" href="Clones.Basic.html#1210" class="Bound">n</a> <a id="1212" class="Symbol">:</a> <a id="1214" href="Agda.Builtin.Nat.html#186" class="Datatype">ℕ</a> <a id="1216" class="Symbol">}</a> <a id="1218" class="Symbol">→</a> <a id="1220" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="1225" href="Clones.Basic.html#563" class="Generalizable">α</a> <a id="1227" class="Symbol">→</a> <a id="1229" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="1234" class="Symbol">(</a><a id="1235" href="Agda.Primitive.html#774" class="Primitive">suc</a> <a id="1239" href="Clones.Basic.html#563" class="Generalizable">α</a><a id="1240" class="Symbol">)</a>
<a id="1242" href="Clones.Basic.html#1199" class="Function">FinRel</a> <a id="1249" class="Symbol">{</a> <a id="1251" class="Argument">n</a> <a id="1253" class="Symbol">=</a> <a id="1255" href="Clones.Basic.html#1255" class="Bound">n</a> <a id="1257" class="Symbol">}</a> <a id="1259" href="Clones.Basic.html#1259" class="Bound">A</a>  <a id="1262" class="Symbol">=</a> <a id="1264" href="Base.Relations.Continuous.html#4456" class="Function">Rel</a> <a id="1268" href="Clones.Basic.html#1259" class="Bound">A</a> <a id="1270" class="Symbol">(</a><a id="1271" href="Data.Fin.Base.html#1135" class="Datatype">Fin</a> <a id="1275" href="Clones.Basic.html#1255" class="Bound">n</a><a id="1276" class="Symbol">)</a>

<a id="FinRels"></a><a id="1279" href="Clones.Basic.html#1279" class="Function">FinRels</a> <a id="1287" class="Symbol">:</a> <a id="1289" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="1294" href="Clones.Basic.html#563" class="Generalizable">α</a> <a id="1296" class="Symbol">→</a> <a id="1298" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="1303" class="Symbol">(</a><a id="1304" href="Agda.Primitive.html#774" class="Primitive">suc</a> <a id="1308" href="Clones.Basic.html#563" class="Generalizable">α</a><a id="1309" class="Symbol">)</a>
<a id="1311" href="Clones.Basic.html#1279" class="Function">FinRels</a> <a id="1319" href="Clones.Basic.html#1319" class="Bound">A</a> <a id="1321" class="Symbol">=</a> <a id="1323" href="Data.Product.html#925" class="Function">Σ[</a> <a id="1326" href="Clones.Basic.html#1326" class="Bound">n</a> <a id="1328" href="Data.Product.html#925" class="Function">∈</a> <a id="1330" href="Agda.Builtin.Nat.html#186" class="Datatype">ℕ</a> <a id="1332" href="Data.Product.html#925" class="Function">]</a> <a id="1334" class="Symbol">(</a><a id="1335" href="Clones.Basic.html#1199" class="Function">FinRel</a> <a id="1342" class="Symbol">{</a><a id="1343" class="Argument">n</a> <a id="1345" class="Symbol">=</a> <a id="1347" href="Clones.Basic.html#1326" class="Bound">n</a><a id="1348" class="Symbol">}</a> <a id="1350" href="Clones.Basic.html#1319" class="Bound">A</a><a id="1351" class="Symbol">)</a>

</pre>
## Clones

Difinimos a un clon de $A$ como un conjunto de operaciones en $A$ que cumple que:

- Contiene todas las proyecciones.
- Es cerrado por composiciones.

<pre class="Agda"><a id="1529" class="Comment">-- Funcion proyeccion, proyecta en la coordenada dada, infiere la aridad</a>
<a id="π"></a><a id="1602" href="Clones.Basic.html#1602" class="Function">π</a> <a id="1604" class="Symbol">:</a> <a id="1606" class="Symbol">{</a><a id="1607" href="Clones.Basic.html#1607" class="Bound">A</a> <a id="1609" class="Symbol">:</a> <a id="1611" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="1616" href="Clones.Basic.html#563" class="Generalizable">α</a><a id="1617" class="Symbol">}</a> <a id="1619" class="Symbol">→</a> <a id="1621" class="Symbol">{</a> <a id="1623" href="Clones.Basic.html#1623" class="Bound">n</a> <a id="1625" class="Symbol">:</a> <a id="1627" href="Agda.Builtin.Nat.html#186" class="Datatype">ℕ</a> <a id="1629" class="Symbol">}</a> <a id="1631" class="Symbol">→</a> <a id="1633" href="Data.Fin.Base.html#1135" class="Datatype">Fin</a> <a id="1637" href="Clones.Basic.html#1623" class="Bound">n</a> <a id="1639" class="Symbol">→</a> <a id="1641" href="Clones.Basic.html#829" class="Function">FinOp</a> <a id="1647" href="Clones.Basic.html#1607" class="Bound">A</a>
<a id="1649" href="Clones.Basic.html#1602" class="Function">π</a> <a id="1651" href="Clones.Basic.html#1651" class="Bound">k</a> <a id="1653" class="Symbol">=</a> <a id="1655" class="Symbol">λ</a> <a id="1657" href="Clones.Basic.html#1657" class="Bound">x</a> <a id="1659" class="Symbol">→</a> <a id="1661" href="Clones.Basic.html#1657" class="Bound">x</a> <a id="1663" href="Clones.Basic.html#1651" class="Bound">k</a> 

<a id="1667" class="Comment">-- Definimos propiedades que tiene que cumplir un Clon</a>
<a id="containsProjections"></a><a id="1722" href="Clones.Basic.html#1722" class="Function">containsProjections</a> <a id="1742" class="Symbol">:</a> <a id="1744" class="Symbol">{</a><a id="1745" href="Clones.Basic.html#1745" class="Bound">A</a> <a id="1747" class="Symbol">:</a> <a id="1749" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="1754" href="Clones.Basic.html#563" class="Generalizable">α</a><a id="1755" class="Symbol">}</a> <a id="1757" class="Symbol">→</a> <a id="1759" href="Relation.Unary.html#1110" class="Function">Pred</a> <a id="1764" class="Symbol">(</a><a id="1765" href="Clones.Basic.html#899" class="Function">FinOps</a> <a id="1772" href="Clones.Basic.html#1745" class="Bound">A</a><a id="1773" class="Symbol">)</a> <a id="1775" href="Clones.Basic.html#565" class="Generalizable">ρ</a> <a id="1777" class="Symbol">→</a> <a id="1779" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="1784" href="Clones.Basic.html#565" class="Generalizable">ρ</a>
<a id="1786" href="Clones.Basic.html#1722" class="Function">containsProjections</a> <a id="1806" href="Clones.Basic.html#1806" class="Bound">F</a> <a id="1808" class="Symbol">=</a> <a id="1810" class="Symbol">∀</a> <a id="1812" class="Symbol">(</a><a id="1813" href="Clones.Basic.html#1813" class="Bound">n</a> <a id="1815" class="Symbol">:</a> <a id="1817" href="Agda.Builtin.Nat.html#186" class="Datatype">ℕ</a><a id="1818" class="Symbol">)</a> <a id="1820" class="Symbol">→</a> <a id="1822" class="Symbol">∀</a> <a id="1824" class="Symbol">(</a><a id="1825" href="Clones.Basic.html#1825" class="Bound">k</a> <a id="1827" class="Symbol">:</a> <a id="1829" href="Data.Fin.Base.html#1135" class="Datatype">Fin</a> <a id="1833" href="Clones.Basic.html#1813" class="Bound">n</a><a id="1834" class="Symbol">)</a> <a id="1836" class="Symbol">→</a> <a id="1838" href="Clones.Basic.html#1806" class="Bound">F</a> <a id="1840" class="Symbol">(</a> <a id="1842" href="Clones.Basic.html#1813" class="Bound">n</a> <a id="1844" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="1846" href="Clones.Basic.html#1602" class="Function">π</a> <a id="1848" class="Symbol">{</a><a id="1849" class="Argument">n</a> <a id="1851" class="Symbol">=</a> <a id="1853" href="Clones.Basic.html#1813" class="Bound">n</a><a id="1854" class="Symbol">}</a> <a id="1856" href="Clones.Basic.html#1825" class="Bound">k</a> <a id="1858" class="Symbol">)</a>

<a id="containsCompositions"></a><a id="1861" href="Clones.Basic.html#1861" class="Function">containsCompositions</a> <a id="1882" class="Symbol">:</a> <a id="1884" class="Symbol">{</a><a id="1885" href="Clones.Basic.html#1885" class="Bound">A</a> <a id="1887" class="Symbol">:</a> <a id="1889" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="1894" href="Clones.Basic.html#563" class="Generalizable">α</a><a id="1895" class="Symbol">}</a> <a id="1897" class="Symbol">→</a> <a id="1899" href="Relation.Unary.html#1110" class="Function">Pred</a> <a id="1904" class="Symbol">(</a><a id="1905" href="Clones.Basic.html#899" class="Function">FinOps</a> <a id="1912" href="Clones.Basic.html#1885" class="Bound">A</a><a id="1913" class="Symbol">)</a> <a id="1915" href="Clones.Basic.html#565" class="Generalizable">ρ</a> <a id="1917" class="Symbol">→</a> <a id="1919" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="1924" class="Symbol">(</a><a id="1925" href="Clones.Basic.html#563" class="Generalizable">α</a> <a id="1927" href="Agda.Primitive.html#804" class="Primitive Operator">⊔</a> <a id="1929" href="Clones.Basic.html#565" class="Generalizable">ρ</a><a id="1930" class="Symbol">)</a>
<a id="1932" href="Clones.Basic.html#1861" class="Function">containsCompositions</a> <a id="1953" class="Symbol">{</a><a id="1954" class="Argument">A</a> <a id="1956" class="Symbol">=</a> <a id="1958" href="Clones.Basic.html#1958" class="Bound">A</a><a id="1959" class="Symbol">}</a> <a id="1961" href="Clones.Basic.html#1961" class="Bound">F</a> <a id="1963" class="Symbol">=</a> <a id="1965" class="Symbol">(</a><a id="1966" href="Clones.Basic.html#1966" class="Bound">n</a> <a id="1968" href="Clones.Basic.html#1968" class="Bound">m</a> <a id="1970" class="Symbol">:</a> <a id="1972" href="Agda.Builtin.Nat.html#186" class="Datatype">ℕ</a><a id="1973" class="Symbol">)(</a><a id="1975" href="Clones.Basic.html#1975" class="Bound">f</a> <a id="1977" class="Symbol">:</a> <a id="1979" href="Clones.Basic.html#829" class="Function">FinOp</a> <a id="1985" class="Symbol">{</a><a id="1986" class="Argument">n</a> <a id="1988" class="Symbol">=</a> <a id="1990" href="Clones.Basic.html#1968" class="Bound">m</a><a id="1991" class="Symbol">}</a> <a id="1993" href="Clones.Basic.html#1958" class="Bound">A</a> <a id="1995" class="Symbol">)(</a><a id="1997" href="Clones.Basic.html#1997" class="Bound">gs</a> <a id="2000" class="Symbol">:</a> <a id="2002" class="Symbol">(</a><a id="2003" href="Data.Fin.Base.html#1135" class="Datatype">Fin</a> <a id="2007" href="Clones.Basic.html#1968" class="Bound">m</a> <a id="2009" class="Symbol">→</a> <a id="2011" href="Clones.Basic.html#829" class="Function">FinOp</a> <a id="2017" class="Symbol">{</a><a id="2018" class="Argument">n</a> <a id="2020" class="Symbol">=</a> <a id="2022" href="Clones.Basic.html#1966" class="Bound">n</a><a id="2023" class="Symbol">}</a> <a id="2025" href="Clones.Basic.html#1958" class="Bound">A</a><a id="2026" class="Symbol">))</a>
                                   <a id="2064" class="Symbol">→</a> <a id="2066" href="Clones.Basic.html#1961" class="Bound">F</a> <a id="2068" class="Symbol">(</a> <a id="2070" href="Clones.Basic.html#1968" class="Bound">m</a> <a id="2072" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="2074" href="Clones.Basic.html#1975" class="Bound">f</a> <a id="2076" class="Symbol">)</a>
                                   <a id="2113" class="Symbol">→</a> <a id="2115" class="Symbol">(∀</a> <a id="2118" class="Symbol">(</a><a id="2119" href="Clones.Basic.html#2119" class="Bound">i</a> <a id="2121" class="Symbol">:</a> <a id="2123" href="Data.Fin.Base.html#1135" class="Datatype">Fin</a> <a id="2127" href="Clones.Basic.html#1968" class="Bound">m</a><a id="2128" class="Symbol">)</a> <a id="2130" class="Symbol">→</a> <a id="2132" href="Clones.Basic.html#1961" class="Bound">F</a> <a id="2134" class="Symbol">(</a> <a id="2136" href="Clones.Basic.html#1966" class="Bound">n</a> <a id="2138" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="2140" href="Clones.Basic.html#1997" class="Bound">gs</a> <a id="2143" href="Clones.Basic.html#2119" class="Bound">i</a> <a id="2145" class="Symbol">))</a>
                                   <a id="2183" class="Symbol">→</a> <a id="2185" href="Clones.Basic.html#1961" class="Bound">F</a> <a id="2187" class="Symbol">(</a> <a id="2189" href="Clones.Basic.html#1966" class="Bound">n</a> <a id="2191" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="2193" class="Symbol">λ</a> <a id="2195" class="Symbol">(</a><a id="2196" href="Clones.Basic.html#2196" class="Bound">xs</a> <a id="2199" class="Symbol">:</a> <a id="2201" class="Symbol">(</a><a id="2202" href="Data.Fin.Base.html#1135" class="Datatype">Fin</a> <a id="2206" href="Clones.Basic.html#1966" class="Bound">n</a> <a id="2208" class="Symbol">→</a> <a id="2210" href="Clones.Basic.html#1958" class="Bound">A</a><a id="2211" class="Symbol">))</a> <a id="2214" class="Symbol">→</a> <a id="2216" href="Clones.Basic.html#1975" class="Bound">f</a> <a id="2218" class="Symbol">(λ</a> <a id="2221" href="Clones.Basic.html#2221" class="Bound">i</a> <a id="2223" class="Symbol">→</a> <a id="2225" href="Clones.Basic.html#1997" class="Bound">gs</a> <a id="2228" href="Clones.Basic.html#2221" class="Bound">i</a> <a id="2230" href="Clones.Basic.html#2196" class="Bound">xs</a><a id="2232" class="Symbol">)</a> <a id="2234" class="Symbol">)</a>
<a id="2236" class="Comment">-- Definimos Clon</a>
<a id="isClon"></a><a id="2254" href="Clones.Basic.html#2254" class="Function">isClon</a> <a id="2261" class="Symbol">:</a> <a id="2263" class="Symbol">{</a><a id="2264" href="Clones.Basic.html#2264" class="Bound">A</a> <a id="2266" class="Symbol">:</a> <a id="2268" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="2273" href="Clones.Basic.html#563" class="Generalizable">α</a><a id="2274" class="Symbol">}</a> <a id="2276" class="Symbol">→</a> <a id="2278" href="Relation.Unary.html#1110" class="Function">Pred</a> <a id="2283" class="Symbol">(</a><a id="2284" href="Clones.Basic.html#899" class="Function">FinOps</a> <a id="2291" href="Clones.Basic.html#2264" class="Bound">A</a><a id="2292" class="Symbol">)</a> <a id="2294" href="Clones.Basic.html#565" class="Generalizable">ρ</a> <a id="2296" class="Symbol">→</a> <a id="2298" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="2303" class="Symbol">(</a><a id="2304" href="Clones.Basic.html#563" class="Generalizable">α</a> <a id="2306" href="Agda.Primitive.html#804" class="Primitive Operator">⊔</a> <a id="2308" href="Clones.Basic.html#565" class="Generalizable">ρ</a><a id="2309" class="Symbol">)</a>
<a id="2311" href="Clones.Basic.html#2254" class="Function">isClon</a> <a id="2318" href="Clones.Basic.html#2318" class="Bound">F</a> <a id="2320" class="Symbol">=</a> <a id="2322" href="Clones.Basic.html#1722" class="Function">containsProjections</a> <a id="2342" href="Clones.Basic.html#2318" class="Bound">F</a> <a id="2344" href="Data.Product.html#1176" class="Function Operator">×</a> <a id="2346" href="Clones.Basic.html#1861" class="Function">containsCompositions</a> <a id="2367" href="Clones.Basic.html#2318" class="Bound">F</a>

<a id="2370" class="Comment">-- Clones : {A : Type α} → Pred (Pred (FinOps A) ρ) (α ⊔ ρ)</a>
<a id="2430" class="Comment">-- Clones = λ F → isClon F </a>

<a id="2459" class="Keyword">record</a> <a id="Clon"></a><a id="2466" href="Clones.Basic.html#2466" class="Record">Clon</a> <a id="2471" class="Symbol">{</a><a id="2472" href="Clones.Basic.html#2472" class="Bound">A</a> <a id="2474" class="Symbol">:</a> <a id="2476" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="2481" href="Clones.Basic.html#563" class="Generalizable">α</a><a id="2482" class="Symbol">}</a> <a id="2484" class="Symbol">:</a> <a id="2486" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="2491" class="Symbol">(</a><a id="2492" href="Clones.Basic.html#2481" class="Bound">α</a> <a id="2494" href="Agda.Primitive.html#804" class="Primitive Operator">⊔</a> <a id="2496" href="Agda.Primitive.html#774" class="Primitive">suc</a> <a id="2500" href="Clones.Basic.html#2500" class="Bound">ρ</a><a id="2501" class="Symbol">)</a> <a id="2503" class="Keyword">where</a>
  <a id="2511" class="Keyword">constructor</a> <a id="mkclon"></a><a id="2523" href="Clones.Basic.html#2523" class="InductiveConstructor">mkclon</a>
  <a id="2532" class="Keyword">field</a>
    <a id="Clon.F"></a><a id="2542" href="Clones.Basic.html#2542" class="Field">F</a>  <a id="2545" class="Symbol">:</a> <a id="2547" href="Relation.Unary.html#1110" class="Function">Pred</a> <a id="2552" class="Symbol">(</a><a id="2553" href="Clones.Basic.html#899" class="Function">FinOps</a> <a id="2560" href="Clones.Basic.html#2472" class="Bound">A</a><a id="2561" class="Symbol">)</a> <a id="2563" href="Clones.Basic.html#2500" class="Bound">ρ</a>
    <a id="Clon.FIsClon"></a><a id="2569" href="Clones.Basic.html#2569" class="Field">FIsClon</a> <a id="2577" class="Symbol">:</a> <a id="2579" href="Clones.Basic.html#2254" class="Function">isClon</a> <a id="2586" href="Clones.Basic.html#2542" class="Field">F</a>

</pre>
### Clon generado

A partir de un conjunto $F$ de operaciones en $A$ podemos hablar del clon generado por $F$ como el menor clon que contiene a $F$. Lo denotamos con [ $F$ ].

<pre class="Agda">
<a id="2779" class="Comment">-- clon generado</a>
<a id="2796" class="Keyword">data</a> <a id="[_]"></a><a id="2801" href="Clones.Basic.html#2801" class="Datatype Operator">[_]</a> <a id="2805" class="Symbol">{</a><a id="2806" href="Clones.Basic.html#2806" class="Bound">A</a> <a id="2808" class="Symbol">:</a> <a id="2810" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="2815" href="Clones.Basic.html#563" class="Generalizable">α</a><a id="2816" class="Symbol">}</a> <a id="2818" class="Symbol">(</a><a id="2819" href="Clones.Basic.html#2819" class="Bound">F</a> <a id="2821" class="Symbol">:</a> <a id="2823" href="Relation.Unary.html#1110" class="Function">Pred</a> <a id="2828" class="Symbol">(</a><a id="2829" href="Clones.Basic.html#899" class="Function">FinOps</a> <a id="2836" href="Clones.Basic.html#2806" class="Bound">A</a><a id="2837" class="Symbol">)</a> <a id="2839" href="Clones.Basic.html#565" class="Generalizable">ρ</a><a id="2840" class="Symbol">)</a> <a id="2842" class="Symbol">:</a> <a id="2844" href="Relation.Unary.html#1110" class="Function">Pred</a> <a id="2849" class="Symbol">(</a><a id="2850" href="Clones.Basic.html#899" class="Function">FinOps</a> <a id="2857" href="Clones.Basic.html#2806" class="Bound">A</a><a id="2858" class="Symbol">)</a> <a id="2860" class="Symbol">(</a><a id="2861" href="Agda.Primitive.html#774" class="Primitive">suc</a> <a id="2865" href="Agda.Primitive.html#758" class="Primitive">Level.zero</a> <a id="2876" href="Agda.Primitive.html#804" class="Primitive Operator">⊔</a> <a id="2878" href="Clones.Basic.html#2815" class="Bound">α</a> <a id="2880" href="Agda.Primitive.html#804" class="Primitive Operator">⊔</a> <a id="2882" href="Clones.Basic.html#2839" class="Bound">ρ</a><a id="2883" class="Symbol">)</a>
  <a id="2887" class="Keyword">where</a>
    <a id="[_].ops"></a><a id="2897" href="Clones.Basic.html#2897" class="InductiveConstructor">ops</a> <a id="2901" class="Symbol">:</a> <a id="2903" class="Symbol">∀</a> <a id="2905" class="Symbol">{</a><a id="2906" href="Clones.Basic.html#2906" class="Bound">f</a><a id="2907" class="Symbol">}</a> <a id="2909" class="Symbol">→</a> <a id="2911" href="Clones.Basic.html#2906" class="Bound">f</a> <a id="2913" href="Relation.Unary.html#1532" class="Function Operator">∈</a> <a id="2915" href="Clones.Basic.html#2819" class="Bound">F</a> <a id="2917" class="Symbol">→</a> <a id="2919" href="Clones.Basic.html#2906" class="Bound">f</a> <a id="2921" href="Relation.Unary.html#1532" class="Function Operator">∈</a> <a id="2923" href="Clones.Basic.html#2801" class="Datatype Operator">[</a> <a id="2925" href="Clones.Basic.html#2819" class="Bound">F</a> <a id="2927" href="Clones.Basic.html#2801" class="Datatype Operator">]</a>
    <a id="[_].projections"></a><a id="2933" href="Clones.Basic.html#2933" class="InductiveConstructor">projections</a> <a id="2945" class="Symbol">:</a> <a id="2947" href="Clones.Basic.html#1722" class="Function">containsProjections</a> <a id="2967" href="Clones.Basic.html#2801" class="Datatype Operator">[</a> <a id="2969" href="Clones.Basic.html#2819" class="Bound">F</a> <a id="2971" href="Clones.Basic.html#2801" class="Datatype Operator">]</a>
    <a id="[_].compositions"></a><a id="2977" href="Clones.Basic.html#2977" class="InductiveConstructor">compositions</a> <a id="2990" class="Symbol">:</a> <a id="2992" href="Clones.Basic.html#1861" class="Function">containsCompositions</a> <a id="3013" href="Clones.Basic.html#2801" class="Datatype Operator">[</a> <a id="3015" href="Clones.Basic.html#2819" class="Bound">F</a> <a id="3017" href="Clones.Basic.html#2801" class="Datatype Operator">]</a>

<a id="GeneratedClonIsClon"></a><a id="3020" href="Clones.Basic.html#3020" class="Function">GeneratedClonIsClon</a> <a id="3040" class="Symbol">:</a> <a id="3042" class="Symbol">{</a><a id="3043" href="Clones.Basic.html#3043" class="Bound">A</a> <a id="3045" class="Symbol">:</a> <a id="3047" href="Clones.Basic.html#235" class="Primitive">Type</a> <a id="3052" href="Clones.Basic.html#563" class="Generalizable">α</a><a id="3053" class="Symbol">}</a> <a id="3055" class="Symbol">{</a><a id="3056" href="Clones.Basic.html#3056" class="Bound">F</a> <a id="3058" class="Symbol">:</a> <a id="3060" href="Relation.Unary.html#1110" class="Function">Pred</a> <a id="3065" class="Symbol">(</a><a id="3066" href="Clones.Basic.html#899" class="Function">FinOps</a> <a id="3073" href="Clones.Basic.html#3043" class="Bound">A</a><a id="3074" class="Symbol">)</a> <a id="3076" href="Clones.Basic.html#565" class="Generalizable">ρ</a><a id="3077" class="Symbol">}</a> <a id="3079" class="Symbol">→</a> <a id="3081" href="Clones.Basic.html#2254" class="Function">isClon</a> <a id="3088" class="Symbol">{</a><a id="3089" class="Argument">A</a> <a id="3091" class="Symbol">=</a> <a id="3093" href="Clones.Basic.html#3043" class="Bound">A</a><a id="3094" class="Symbol">}</a> <a id="3096" href="Clones.Basic.html#2801" class="Datatype Operator">[</a> <a id="3098" href="Clones.Basic.html#3056" class="Bound">F</a> <a id="3100" href="Clones.Basic.html#2801" class="Datatype Operator">]</a>
<a id="3102" href="Clones.Basic.html#3020" class="Function">GeneratedClonIsClon</a>  <a id="3123" class="Symbol">=</a> <a id="3125" href="Clones.Basic.html#2933" class="InductiveConstructor">projections</a> <a id="3137" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="3139" href="Clones.Basic.html#2977" class="InductiveConstructor">compositions</a>

</pre>