import PlattAssemblyKernel
import PlattCertificates.Count131072.C030064
import PlattCertificates.Count131072.C030065
import PlattCertificates.Count131072.C030066
import PlattCertificates.Count131072.C030067
import PlattCertificates.Count131072.C030068
import PlattCertificates.Count131072.C030069
import PlattCertificates.Count131072.C030070
import PlattCertificates.Count131072.C030071
import PlattCertificates.Count131072.C030072
import PlattCertificates.Count131072.C030073
import PlattCertificates.Count131072.C030074
import PlattCertificates.Count131072.C030075
import PlattCertificates.Count131072.C030076
import PlattCertificates.Count131072.C030077
import PlattCertificates.Count131072.C030078
import PlattCertificates.Count131072.C030079
import PlattCertificates.Count131072.C030080
import PlattCertificates.Count131072.C030081
import PlattCertificates.Count131072.C030082
import PlattCertificates.Count131072.C030083
import PlattCertificates.Count131072.C030084
import PlattCertificates.Count131072.C030085
import PlattCertificates.Count131072.C030086
import PlattCertificates.Count131072.C030087
import PlattCertificates.Count131072.C030088
import PlattCertificates.Count131072.C030089
import PlattCertificates.Count131072.C030090
import PlattCertificates.Count131072.C030091
import PlattCertificates.Count131072.C030092
import PlattCertificates.Count131072.C030093
import PlattCertificates.Count131072.C030094
import PlattCertificates.Count131072.C030095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30064 : List PrefixCut := [⟨40,130586606,130586679⟩,
⟨128,423438294,423438535⟩]
theorem checked30064 : checkPrefixCuts (2^48) 3944480769 9 Manual.Count131072.C030064.packed 128 cuts30064 = true := by
 decide +kernel
def pointBounds30064 : List (Nat × Nat × Nat) := [(3944521728,105255227927396,105255611263979)]
theorem point_links_checked30064 : (cuts30064.take 1).map (fun c => (3944480769-1+2*2^9*c.k,105255097340790+c.lower,105255480677300+c.upper)) = pointBounds30064 := by
 decide +kernel
def cuts30065 : List PrefixCut := [⟨33,111815631,111815694⟩,
⟨128,422068504,422068741⟩]
theorem checked30065 : checkPrefixCuts (2^48) 3944611841 9 Manual.Count131072.C030065.packed 128 cuts30065 = true := by
 decide +kernel
def pointBounds30065 : List (Nat × Nat × Nat) := [(3944645632,105255632594715,105256015931529)]
theorem point_links_checked30065 : (cuts30065.take 1).map (fun c => (3944611841-1+2*2^9*c.k,105255520779084+c.lower,105255904115835+c.upper)) = pointBounds30065 := by
 decide +kernel
def cuts30066 : List PrefixCut := [⟨26,84412016,84412063⟩,
⟨128,419771151,419771383⟩]
theorem checked30066 : checkPrefixCuts (2^48) 3944742913 9 Manual.Count131072.C030066.packed 128 cuts30066 = true := by
 decide +kernel
def pointBounds30066 : List (Nat × Nat × Nat) := [(3944769536,105256027259604,105256410596639)]
theorem point_links_checked30066 : (cuts30066.take 1).map (fun c => (3944742913-1+2*2^9*c.k,105255942847588+c.lower,105256326184576+c.upper)) = pointBounds30066 := by
 decide +kernel
def cuts30067 : List PrefixCut := [⟨19,62861008,62861044⟩,
⟨128,420827452,420827692⟩]
theorem checked30067 : checkPrefixCuts (2^48) 3944873985 9 Manual.Count131072.C030067.packed 128 cuts30067 = true := by
 decide +kernel
def pointBounds30067 : List (Nat × Nat × Nat) := [(3944893440,105256425479747,105256808817003)]
theorem point_links_checked30067 : (cuts30067.take 1).map (fun c => (3944873985-1+2*2^9*c.k,105256362618739+c.lower,105256745955959+c.upper)) = pointBounds30067 := by
 decide +kernel
def cuts30068 : List PrefixCut := [⟨12,40954657,40954679⟩,
⟨128,425451115,425451349⟩]
theorem checked30068 : checkPrefixCuts (2^48) 3945005057 9 Manual.Count131072.C030068.packed 128 cuts30068 = true := by
 decide +kernel
def pointBounds30068 : List (Nat × Nat × Nat) := [(3945017344,105256824400848,105257207738330)]
theorem point_links_checked30068 : (cuts30068.take 1).map (fun c => (3945005057-1+2*2^9*c.k,105256783446191+c.lower,105257166783651+c.upper)) = pointBounds30068 := by
 decide +kernel
def cuts30069 : List PrefixCut := [⟨5,14768885,14768895⟩,
⟨126,417089537,417089777⟩,
⟨128,424081344,424081588⟩]
theorem checked30069 : checkPrefixCuts (2^48) 3945136129 9 Manual.Count131072.C030069.packed 128 cuts30069 = true := by
 decide +kernel
def pointBounds30069 : List (Nat × Nat × Nat) := [(3945141248,105257223666191,105257607003895),(3945265152,105257625986843,105258009324777)]
theorem point_links_checked30069 : (cuts30069.take 2).map (fun c => (3945136129-1+2*2^9*c.k,105257208897306+c.lower,105257592235000+c.upper)) = pointBounds30069 := by
 decide +kernel
def cuts30070 : List PrefixCut := [⟨119,393675442,393675659⟩,
⟨128,420357598,420357830⟩]
theorem checked30070 : checkPrefixCuts (2^48) 3945267201 9 Manual.Count131072.C030070.packed 128 cuts30070 = true := by
 decide +kernel
def pointBounds30070 : List (Nat × Nat × Nat) := [(3945389056,105258026654092,105258409992247)]
theorem point_links_checked30070 : (cuts30070.take 1).map (fun c => (3945267201-1+2*2^9*c.k,105257632978650+c.lower,105258016316588+c.upper)) = pointBounds30070 := by
 decide +kernel
def cuts30071 : List PrefixCut := [⟨112,368621803,368622009⟩,
⟨128,419844176,419844411⟩]
theorem checked30071 : checkPrefixCuts (2^48) 3945398273 9 Manual.Count131072.C030071.packed 128 cuts30071 = true := by
 decide +kernel
def pointBounds30071 : List (Nat × Nat × Nat) := [(3945512960,105258421958051,105258805296427)]
theorem point_links_checked30071 : (cuts30071.take 1).map (fun c => (3945398273-1+2*2^9*c.k,105258053336248+c.lower,105258436674418+c.upper)) = pointBounds30071 := by
 decide +kernel
def cuts30072 : List PrefixCut := [⟨105,342927700,342927893⟩,
⟨128,421613571,421613806⟩]
theorem checked30072 : checkPrefixCuts (2^48) 3945529345 9 Manual.Count131072.C030072.packed 128 cuts30072 = true := by
 decide +kernel
def pointBounds30072 : List (Nat × Nat × Nat) := [(3945636864,105258816108124,105259199446722)]
theorem point_links_checked30072 : (cuts30072.take 1).map (fun c => (3945529345-1+2*2^9*c.k,105258473180424+c.lower,105258856518829+c.upper)) = pointBounds30072 := by
 decide +kernel
def cuts30073 : List PrefixCut := [⟨98,323869681,323869859⟩,
⟨128,424096406,424096641⟩]
theorem checked30073 : checkPrefixCuts (2^48) 3945660417 9 Manual.Count131072.C030073.packed 128 cuts30073 = true := by
 decide +kernel
def pointBounds30073 : List (Nat × Nat × Nat) := [(3945760768,105259218663676,105259602002494)]
theorem point_links_checked30073 : (cuts30073.take 1).map (fun c => (3945660417-1+2*2^9*c.k,105258894793995+c.lower,105259278132635+c.upper)) = pointBounds30073 := by
 decide +kernel
def cuts30074 : List PrefixCut := [⟨91,299890749,299890912⟩,
⟨128,422584280,422584515⟩]
theorem checked30074 : checkPrefixCuts (2^48) 3945791489 9 Manual.Count131072.C030074.packed 128 cuts30074 = true := by
 decide +kernel
def pointBounds30074 : List (Nat × Nat × Nat) := [(3945884672,105259618781150,105260002120188)]
theorem point_links_checked30074 : (cuts30074.take 1).map (fun c => (3945791489-1+2*2^9*c.k,105259318890401+c.lower,105259702229276+c.upper)) = pointBounds30074 := by
 decide +kernel
def cuts30075 : List PrefixCut := [⟨84,278053416,278053577⟩,
⟨128,423996932,423997177⟩]
theorem checked30075 : checkPrefixCuts (2^48) 3945922561 9 Manual.Count131072.C030075.packed 128 cuts30075 = true := by
 decide +kernel
def pointBounds30075 : List (Nat × Nat × Nat) := [(3946008576,105260019528097,105260402867368)]
theorem point_links_checked30075 : (cuts30075.take 1).map (fun c => (3945922561-1+2*2^9*c.k,105259741474681+c.lower,105260124813791+c.upper)) = pointBounds30075 := by
 decide +kernel
def cuts30076 : List PrefixCut := [⟨77,255361484,255361624⟩,
⟨128,423269569,423269805⟩]
theorem checked30076 : checkPrefixCuts (2^48) 3946053633 9 Manual.Count131072.C030076.packed 128 cuts30076 = true := by
 decide +kernel
def pointBounds30076 : List (Nat × Nat × Nat) := [(3946132480,105260420833097,105260804172592)]
theorem point_links_checked30076 : (cuts30076.take 1).map (fun c => (3946053633-1+2*2^9*c.k,105260165471613+c.lower,105260548810968+c.upper)) = pointBounds30076 := by
 decide +kernel
def cuts30077 : List PrefixCut := [⟨70,234953463,234953600⟩,
⟨128,427107128,427107373⟩]
theorem checked30077 : checkPrefixCuts (2^48) 3946184705 9 Manual.Count131072.C030077.packed 128 cuts30077 = true := by
 decide +kernel
def pointBounds30077 : List (Nat × Nat × Nat) := [(3946256384,105260823694645,105261207034373)]
theorem point_links_checked30077 : (cuts30077.take 1).map (fun c => (3946184705-1+2*2^9*c.k,105260588741182+c.lower,105260972080773+c.upper)) = pointBounds30077 := by
 decide +kernel
def cuts30078 : List PrefixCut := [⟨63,204418609,204418729⟩,
⟨128,424311198,424311441⟩]
theorem checked30078 : checkPrefixCuts (2^48) 3946315777 9 Manual.Count131072.C030078.packed 128 cuts30078 = true := by
 decide +kernel
def pointBounds30078 : List (Nat × Nat × Nat) := [(3946380288,105261220266919,105261603606875)]
theorem point_links_checked30078 : (cuts30078.take 1).map (fun c => (3946315777-1+2*2^9*c.k,105261015848310+c.lower,105261399188146+c.upper)) = pointBounds30078 := by
 decide +kernel
def cuts30079 : List PrefixCut := [⟨56,183514355,183514459⟩,
⟨128,420873706,420873945⟩]
theorem checked30079 : checkPrefixCuts (2^48) 3946446849 9 Manual.Count131072.C030079.packed 128 cuts30079 = true := by
 decide +kernel
def pointBounds30079 : List (Nat × Nat × Nat) := [(3946504192,105261623673863,105262007014046)]
theorem point_links_checked30079 : (cuts30079.take 1).map (fun c => (3946446849-1+2*2^9*c.k,105261440159508+c.lower,105261823499587+c.upper)) = pointBounds30079 := by
 decide +kernel
def cuts30080 : List PrefixCut := [⟨49,160257840,160257932⟩,
⟨128,421858200,421858437⟩]
theorem checked30080 : checkPrefixCuts (2^48) 3946577921 9 Manual.Count131072.C030080.packed 128 cuts30080 = true := by
 decide +kernel
def pointBounds30080 : List (Nat × Nat × Nat) := [(3946628096,105262021291054,105262404631464)]
theorem point_links_checked30080 : (cuts30080.take 1).map (fun c => (3946577921-1+2*2^9*c.k,105261861033214+c.lower,105262244373532+c.upper)) = pointBounds30080 := by
 decide +kernel
def cuts30081 : List PrefixCut := [⟨42,140283479,140283558⟩,
⟨128,431400754,431400996⟩]
theorem checked30081 : checkPrefixCuts (2^48) 3946708993 9 Manual.Count131072.C030081.packed 128 cuts30081 = true := by
 decide +kernel
def pointBounds30081 : List (Nat × Nat × Nat) := [(3946752000,105262423174893,105262806515527)]
theorem point_links_checked30081 : (cuts30081.take 1).map (fun c => (3946708993-1+2*2^9*c.k,105262282891414+c.lower,105262666231969+c.upper)) = pointBounds30081 := by
 decide +kernel
def cuts30082 : List PrefixCut := [⟨35,116388035,116388102⟩,
⟨128,422329447,422329688⟩]
theorem checked30082 : checkPrefixCuts (2^48) 3946840065 9 Manual.Count131072.C030082.packed 128 cuts30082 = true := by
 decide +kernel
def pointBounds30082 : List (Nat × Nat × Nat) := [(3946875904,105262830680203,105263214021067)]
theorem point_links_checked30082 : (cuts30082.take 1).map (fun c => (3946840065-1+2*2^9*c.k,105262714292168+c.lower,105263097632965+c.upper)) = pointBounds30082 := by
 decide +kernel
def cuts30083 : List PrefixCut := [⟨28,92280178,92280230⟩,
⟨128,423741636,423741872⟩]
theorem checked30083 : checkPrefixCuts (2^48) 3946971137 9 Manual.Count131072.C030083.packed 128 cuts30083 = true := by
 decide +kernel
def pointBounds30083 : List (Nat × Nat × Nat) := [(3946999808,105263228901793,105263612242883)]
theorem point_links_checked30083 : (cuts30083.take 1).map (fun c => (3946971137-1+2*2^9*c.k,105263136621615+c.lower,105263519962653+c.upper)) = pointBounds30083 := by
 decide +kernel
def cuts30084 : List PrefixCut := [⟨21,70527163,70527201⟩,
⟨128,425296418,425296653⟩]
theorem checked30084 : checkPrefixCuts (2^48) 3947102209 9 Manual.Count131072.C030084.packed 128 cuts30084 = true := by
 decide +kernel
def pointBounds30084 : List (Nat × Nat × Nat) := [(3947123712,105263630890414,105264014231726)]
theorem point_links_checked30084 : (cuts30084.take 1).map (fun c => (3947102209-1+2*2^9*c.k,105263560363251+c.lower,105263943704525+c.upper)) = pointBounds30084 := by
 decide +kernel
def cuts30085 : List PrefixCut := [⟨14,43641281,43641306⟩,
⟨128,420718502,420718743⟩]
theorem checked30085 : checkPrefixCuts (2^48) 3947233281 9 Manual.Count131072.C030085.packed 128 cuts30085 = true := by
 decide +kernel
def pointBounds30085 : List (Nat × Nat × Nat) := [(3947247616,105264029300950,105264412642484)]
theorem point_links_checked30085 : (cuts30085.take 1).map (fun c => (3947233281-1+2*2^9*c.k,105263985659669+c.lower,105264369001178+c.upper)) = pointBounds30085 := by
 decide +kernel
def cuts30086 : List PrefixCut := [⟨7,23459998,23460011⟩,
⟨128,429047385,429047621⟩]
theorem checked30086 : checkPrefixCuts (2^48) 3947364353 9 Manual.Count131072.C030086.packed 128 cuts30086 = true := by
 decide +kernel
def pointBounds30086 : List (Nat × Nat × Nat) := [(3947371520,105264429838169,105264813179932),(3947495424,105264835425556,105265218767542)]
theorem point_links_checked30086 : (cuts30086.take 2).map (fun c => (3947364353-1+2*2^9*c.k,105264406378171+c.lower,105264789719921+c.upper)) = pointBounds30086 := by
 decide +kernel
def cuts30087 : List PrefixCut := [⟨121,398159055,398159279⟩,
⟨128,420761911,420762147⟩]
theorem checked30087 : checkPrefixCuts (2^48) 3947495425 9 Manual.Count131072.C030087.packed 128 cuts30087 = true := by
 decide +kernel
def pointBounds30087 : List (Nat × Nat × Nat) := [(3947619328,105265233584611,105265616926821)]
theorem point_links_checked30087 : (cuts30087.take 1).map (fun c => (3947495425-1+2*2^9*c.k,105264835425556+c.lower,105265218767542+c.upper)) = pointBounds30087 := by
 decide +kernel
def cuts30088 : List PrefixCut := [⟨114,378039218,378039433⟩,
⟨128,426095467,426095709⟩]
theorem checked30088 : checkPrefixCuts (2^48) 3947626497 9 Manual.Count131072.C030088.packed 128 cuts30088 = true := by
 decide +kernel
def pointBounds30088 : List (Nat × Nat × Nat) := [(3947743232,105265634226685,105266017569122)]
theorem point_links_checked30088 : (cuts30088.take 1).map (fun c => (3947626497-1+2*2^9*c.k,105265256187467+c.lower,105265639529689+c.upper)) = pointBounds30088 := by
 decide +kernel
def cuts30089 : List PrefixCut := [⟨107,349436197,349436396⟩,
⟨128,419735797,419736038⟩]
theorem checked30089 : checkPrefixCuts (2^48) 3947757569 9 Manual.Count131072.C030089.packed 128 cuts30089 = true := by
 decide +kernel
def pointBounds30089 : List (Nat × Nat × Nat) := [(3947867136,105266031719131,105266415061794)]
theorem point_links_checked30089 : (cuts30089.take 1).map (fun c => (3947757569-1+2*2^9*c.k,105265682282934+c.lower,105266065625398+c.upper)) = pointBounds30089 := by
 decide +kernel
def cuts30090 : List PrefixCut := [⟨100,326681292,326681476⟩,
⟨128,419793169,419793403⟩]
theorem checked30090 : checkPrefixCuts (2^48) 3947888641 9 Manual.Count131072.C030090.packed 128 cuts30090 = true := by
 decide +kernel
def pointBounds30090 : List (Nat × Nat × Nat) := [(3947991040,105266428700023,105266812042912)]
theorem point_links_checked30090 : (cuts30090.take 1).map (fun c => (3947888641-1+2*2^9*c.k,105266102018731+c.lower,105266485361436+c.upper)) = pointBounds30090 := by
 decide +kernel
def cuts30091 : List PrefixCut := [⟨93,305424980,305425158⟩,
⟨128,423700340,423700584⟩]
theorem checked30091 : checkPrefixCuts (2^48) 3948019713 9 Manual.Count131072.C030091.packed 128 cuts30091 = true := by
 decide +kernel
def pointBounds30091 : List (Nat × Nat × Nat) := [(3948114944,105266827236880,105267210579997)]
theorem point_links_checked30091 : (cuts30091.take 1).map (fun c => (3948019713-1+2*2^9*c.k,105266521811900+c.lower,105266905154839+c.upper)) = pointBounds30091 := by
 decide +kernel
def cuts30092 : List PrefixCut := [⟨86,284597854,284598021⟩,
⟨128,425896354,425896601⟩]
theorem checked30092 : checkPrefixCuts (2^48) 3948150785 9 Manual.Count131072.C030092.packed 128 cuts30092 = true := by
 decide +kernel
def pointBounds30092 : List (Nat × Nat × Nat) := [(3948238848,105267230110094,105267613453444)]
theorem point_links_checked30092 : (cuts30092.take 1).map (fun c => (3948150785-1+2*2^9*c.k,105266945512240+c.lower,105267328855423+c.upper)) = pointBounds30092 := by
 decide +kernel
def cuts30093 : List PrefixCut := [⟨79,261276928,261277075⟩,
⟨128,421105897,421106135⟩]
theorem checked30093 : checkPrefixCuts (2^48) 3948281857 9 Manual.Count131072.C030093.packed 128 cuts30093 = true := by
 decide +kernel
def pointBounds30093 : List (Nat × Nat × Nat) := [(3948362752,105267632685522,105268016029099)]
theorem point_links_checked30093 : (cuts30093.take 1).map (fun c => (3948281857-1+2*2^9*c.k,105267371408594+c.lower,105267754752024+c.upper)) = pointBounds30093 := by
 decide +kernel
def cuts30094 : List PrefixCut := [⟨72,235533730,235533867⟩,
⟨128,421091898,421092136⟩]
theorem checked30094 : checkPrefixCuts (2^48) 3948412929 9 Manual.Count131072.C030094.packed 128 cuts30094 = true := by
 decide +kernel
def pointBounds30094 : List (Nat × Nat × Nat) := [(3948486656,105268028048221,105268411392026)]
theorem point_links_checked30094 : (cuts30094.take 1).map (fun c => (3948412929-1+2*2^9*c.k,105267792514491+c.lower,105268175858159+c.upper)) = pointBounds30094 := by
 decide +kernel
def cuts30095 : List PrefixCut := [⟨65,213213855,213213975⟩,
⟨128,425568786,425569022⟩]
theorem checked30095 : checkPrefixCuts (2^48) 3948544001 9 Manual.Count131072.C030095.packed 128 cuts30095 = true := by
 decide +kernel
def pointBounds30095 : List (Nat × Nat × Nat) := [(3948610560,105268426820244,105268810164270)]
theorem point_links_checked30095 : (cuts30095.take 1).map (fun c => (3948544001-1+2*2^9*c.k,105268213606389+c.lower,105268596950295+c.upper)) = pointBounds30095 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000002
