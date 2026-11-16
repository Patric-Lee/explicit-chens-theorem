import PlattAssemblyKernel
import PlattCertificates.Count131072.C018160
import PlattCertificates.Count131072.C018161
import PlattCertificates.Count131072.C018162
import PlattCertificates.Count131072.C018163
import PlattCertificates.Count131072.C018164
import PlattCertificates.Count131072.C018165
import PlattCertificates.Count131072.C018166
import PlattCertificates.Count131072.C018167
import PlattCertificates.Count131072.C018168
import PlattCertificates.Count131072.C018169
import PlattCertificates.Count131072.C018170
import PlattCertificates.Count131072.C018171
import PlattCertificates.Count131072.C018172
import PlattCertificates.Count131072.C018173
import PlattCertificates.Count131072.C018174
import PlattCertificates.Count131072.C018175
import PlattCertificates.Count131072.C018176
import PlattCertificates.Count131072.C018177
import PlattCertificates.Count131072.C018178
import PlattCertificates.Count131072.C018179
import PlattCertificates.Count131072.C018180
import PlattCertificates.Count131072.C018181
import PlattCertificates.Count131072.C018182
import PlattCertificates.Count131072.C018183
import PlattCertificates.Count131072.C018184
import PlattCertificates.Count131072.C018185
import PlattCertificates.Count131072.C018186
import PlattCertificates.Count131072.C018187
import PlattCertificates.Count131072.C018188
import PlattCertificates.Count131072.C018189
import PlattCertificates.Count131072.C018190
import PlattCertificates.Count131072.C018191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000255
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18160 : List PrefixCut := [⟨65,364913510,364913735⟩,
⟨128,716122798,716123234⟩]
theorem checked18160 : checkPrefixCuts (2^48) 2384199681 9 Manual.Count131072.C018160.packed 128 cuts18160 = true := by
 decide +kernel
def pointBounds18160 : List (Nat × Nat × Nat) := [(2384266240,98767823454909,98768203075839)]
theorem point_links_checked18160 : (cuts18160.take 1).map (fun c => (2384199681-1+2*2^9*c.k,98767458541399+c.lower,98767838162104+c.upper)) = pointBounds18160 := by
 decide +kernel
def cuts18161 : List PrefixCut := [⟨10,54303783,54303814⟩,
⟨83,463345661,463345944⟩,
⟨128,712305947,712306382⟩]
theorem checked18161 : checkPrefixCuts (2^48) 2384330753 9 Manual.Count131072.C018161.packed 128 cuts18161 = true := by
 decide +kernel
def pointBounds18161 : List (Nat × Nat × Nat) := [(2384340992,98768228967980,98768608589152),(2384415744,98768638009858,98769017631282)]
theorem point_links_checked18161 : (cuts18161.take 2).map (fun c => (2384330753-1+2*2^9*c.k,98768174664197+c.lower,98768554285338+c.upper)) = pointBounds18161 := by
 decide +kernel
def cuts18162 : List PrefixCut := [⟨28,156881469,156881563⟩,
⟨101,560467705,560468047⟩,
⟨128,712738869,712739297⟩]
theorem checked18162 : checkPrefixCuts (2^48) 2384461825 9 Manual.Count131072.C018162.packed 128 cuts18162 = true := by
 decide +kernel
def pointBounds18162 : List (Nat × Nat × Nat) := [(2384490496,98769043851613,98769423473283),(2384565248,98769447437849,98769827059767)]
theorem point_links_checked18162 : (cuts18162.take 2).map (fun c => (2384461825-1+2*2^9*c.k,98768886970144+c.lower,98769266591720+c.upper)) = pointBounds18162 := by
 decide +kernel
def cuts18163 : List PrefixCut := [⟨46,255079679,255079839⟩,
⟨119,665958814,665959229⟩,
⟨128,717657142,717657588⟩]
theorem checked18163 : checkPrefixCuts (2^48) 2384592897 9 Manual.Count131072.C018163.packed 128 cuts18163 = true := by
 decide +kernel
def pointBounds18163 : List (Nat × Nat × Nat) := [(2384640000,98769854788692,98770234410856),(2384714752,98770265667827,98770645290246)]
theorem point_links_checked18163 : (cuts18163.take 2).map (fun c => (2384592897-1+2*2^9*c.k,98769599709013+c.lower,98769979331017+c.upper)) = pointBounds18163 := by
 decide +kernel
def cuts18164 : List PrefixCut := [⟨64,363298995,363299214⟩,
⟨128,722693065,722693503⟩]
theorem checked18164 : checkPrefixCuts (2^48) 2384723969 9 Manual.Count131072.C018164.packed 128 cuts18164 = true := by
 decide +kernel
def pointBounds18164 : List (Nat × Nat × Nat) := [(2384789504,98770680665150,98771060287819)]
theorem point_links_checked18164 : (cuts18164.take 1).map (fun c => (2384723969-1+2*2^9*c.k,98770317366155+c.lower,98770696988605+c.upper)) = pointBounds18164 := by
 decide +kernel
def cuts18165 : List PrefixCut := [⟨9,51577265,51577294⟩,
⟨82,451795626,451795904⟩,
⟨128,713919518,713919954⟩]
theorem checked18165 : checkPrefixCuts (2^48) 2384855041 9 Manual.Count131072.C018165.packed 128 cuts18165 = true := by
 decide +kernel
def pointBounds18165 : List (Nat × Nat × Nat) := [(2384864256,98771091636485,98771471259402),(2384939008,98771491854846,98771871478012)]
theorem point_links_checked18165 : (cuts18165.take 2).map (fun c => (2384855041-1+2*2^9*c.k,98771040059220+c.lower,98771419682108+c.upper)) = pointBounds18165 := by
 decide +kernel
def cuts18166 : List PrefixCut := [⟨27,150710062,150710154⟩,
⟨100,553381656,553381990⟩,
⟨128,713526308,713526737⟩]
theorem checked18166 : checkPrefixCuts (2^48) 2384986113 9 Manual.Count131072.C018166.packed 128 cuts18166 = true := by
 decide +kernel
def pointBounds18166 : List (Nat × Nat × Nat) := [(2385013760,98771904688800,98772284312216),(2385088512,98772307360394,98772686984052)]
theorem point_links_checked18166 : (cuts18166.take 2).map (fun c => (2384986113-1+2*2^9*c.k,98771753978738+c.lower,98772133602062+c.upper)) = pointBounds18166 := by
 decide +kernel
def cuts18167 : List PrefixCut := [⟨45,254315594,254315749⟩,
⟨118,652713616,652714010⟩,
⟨128,705580658,705581086⟩]
theorem checked18167 : checkPrefixCuts (2^48) 2385117185 9 Manual.Count131072.C018167.packed 128 cuts18167 = true := by
 decide +kernel
def pointBounds18167 : List (Nat × Nat × Nat) := [(2385163264,98772721820640,98773101444548),(2385238016,98773120218662,98773499842809)]
theorem point_links_checked18167 : (cuts18167.take 2).map (fun c => (2385117185-1+2*2^9*c.k,98772467505046+c.lower,98772847128799+c.upper)) = pointBounds18167 := by
 decide +kernel
def cuts18168 : List PrefixCut := [⟨63,351890721,351890929⟩,
⟨128,718285973,718286402⟩]
theorem checked18168 : checkPrefixCuts (2^48) 2385248257 9 Manual.Count131072.C018168.packed 128 cuts18168 = true := by
 decide +kernel
def pointBounds18168 : List (Nat × Nat × Nat) := [(2385312768,98773524976425,98773904600814)]
theorem point_links_checked18168 : (cuts18168.take 1).map (fun c => (2385248257-1+2*2^9*c.k,98773173085704+c.lower,98773552709885+c.upper)) = pointBounds18168 := by
 decide +kernel
def cuts18169 : List PrefixCut := [⟨8,42361946,42361974⟩,
⟨81,448274375,448274650⟩,
⟨128,715414560,715414994⟩]
theorem checked18169 : checkPrefixCuts (2^48) 2385379329 9 Manual.Count131072.C018169.packed 128 cuts18169 = true := by
 decide +kernel
def pointBounds18169 : List (Nat × Nat × Nat) := [(2385387520,98773933733623,98774313358261),(2385462272,98774339646052,98774719270937)]
theorem point_links_checked18169 : (cuts18169.take 2).map (fun c => (2385379329-1+2*2^9*c.k,98773891371677+c.lower,98774270996287+c.upper)) = pointBounds18169 := by
 decide +kernel
def cuts18170 : List PrefixCut := [⟨26,144659302,144659391⟩,
⟨99,552434250,552434590⟩,
⟨128,714549528,714549970⟩]
theorem checked18170 : checkPrefixCuts (2^48) 2385510401 9 Manual.Count131072.C018170.packed 128 cuts18170 = true := by
 decide +kernel
def pointBounds18170 : List (Nat × Nat × Nat) := [(2385537024,98774751445539,98775131070672),(2385611776,98775159220487,98775538845871)]
theorem point_links_checked18170 : (cuts18170.take 2).map (fun c => (2385510401-1+2*2^9*c.k,98774606786237+c.lower,98774986411281+c.upper)) = pointBounds18170 := by
 decide +kernel
def cuts18171 : List PrefixCut := [⟨44,244584930,244585083⟩,
⟨117,656109624,656110027⟩,
⟨128,718049592,718050032⟩]
theorem checked18171 : checkPrefixCuts (2^48) 2385641473 9 Manual.Count131072.C018171.packed 128 cuts18171 = true := by
 decide +kernel
def pointBounds18171 : List (Nat × Nat × Nat) := [(2385686528,98775565920695,98775945546334),(2385761280,98775977445389,98776357071278)]
theorem point_links_checked18171 : (cuts18171.take 2).map (fun c => (2385641473-1+2*2^9*c.k,98775321335765+c.lower,98775700961251+c.upper)) = pointBounds18171 := by
 decide +kernel
def cuts18172 : List PrefixCut := [⟨62,349453855,349454068⟩,
⟨128,721195501,721195939⟩]
theorem checked18172 : checkPrefixCuts (2^48) 2385772545 9 Manual.Count131072.C018172.packed 128 cuts18172 = true := by
 decide +kernel
def pointBounds18172 : List (Nat × Nat × Nat) := [(2385836032,98776388839212,98776768465351)]
theorem point_links_checked18172 : (cuts18172.take 1).map (fun c => (2385772545-1+2*2^9*c.k,98776039385357+c.lower,98776419011283+c.upper)) = pointBounds18172 := by
 decide +kernel
def cuts18173 : List PrefixCut := [⟨7,37869637,37869658⟩,
⟨80,446760310,446760574⟩,
⟨128,721745753,721746181⟩]
theorem checked18173 : checkPrefixCuts (2^48) 2385903617 9 Manual.Count131072.C018173.packed 128 cuts18173 = true := by
 decide +kernel
def pointBounds18173 : List (Nat × Nat × Nat) := [(2385910784,98776798450495,98777178076880),(2385985536,98777207341168,98777586967796)]
theorem point_links_checked18173 : (cuts18173.take 2).map (fun c => (2385903617-1+2*2^9*c.k,98776760580858+c.lower,98777140207222+c.upper)) = pointBounds18173 := by
 decide +kernel
def cuts18174 : List PrefixCut := [⟨25,141914329,141914414⟩,
⟨98,551015291,551015622⟩,
⟨128,716869767,716870201⟩]
theorem checked18174 : checkPrefixCuts (2^48) 2386034689 9 Manual.Count131072.C018174.packed 128 cuts18174 = true := by
 decide +kernel
def pointBounds18174 : List (Nat × Nat × Nat) := [(2386060288,98777624240940,98778003867817),(2386135040,98778033341902,98778412969025)]
theorem point_links_checked18174 : (cuts18174.take 2).map (fun c => (2386034689-1+2*2^9*c.k,98777482326611+c.lower,98777861953403+c.upper)) = pointBounds18174 := by
 decide +kernel
def cuts18175 : List PrefixCut := [⟨43,244649154,244649299⟩,
⟨116,655257966,655258362⟩,
⟨128,721548663,721549099⟩]
theorem checked18175 : checkPrefixCuts (2^48) 2386165761 9 Manual.Count131072.C018175.packed 128 cuts18175 = true := by
 decide +kernel
def pointBounds18175 : List (Nat × Nat × Nat) := [(2386209792,98778443845532,98778823472903),(2386284544,98778854454344,98779234081966)]
theorem point_links_checked18175 : (cuts18175.take 2).map (fun c => (2386165761-1+2*2^9*c.k,98778199196378+c.lower,98778578823604+c.upper)) = pointBounds18175 := by
 decide +kernel
def cuts18176 : List PrefixCut := [⟨61,335340788,335340995⟩,
⟨128,710775296,710775734⟩]
theorem checked18176 : checkPrefixCuts (2^48) 2386296833 9 Manual.Count131072.C018176.packed 128 cuts18176 = true := by
 decide +kernel
def pointBounds18176 : List (Nat × Nat × Nat) := [(2386359296,98779256085829,98779635713698)]
theorem point_links_checked18176 : (cuts18176.take 1).map (fun c => (2386296833-1+2*2^9*c.k,98778920745041+c.lower,98779300372703+c.upper)) = pointBounds18176 := by
 decide +kernel
def cuts18177 : List PrefixCut := [⟨6,30194701,30194720⟩,
⟨79,438170150,438170417⟩,
⟨128,710028660,710029095⟩]
theorem checked18177 : checkPrefixCuts (2^48) 2386427905 9 Manual.Count131072.C018177.packed 128 cuts18177 = true := by
 decide +kernel
def pointBounds18177 : List (Nat × Nat × Nat) := [(2386434048,98779661715038,98780041343157),(2386508800,98780069690487,98780449318854)]
theorem point_links_checked18177 : (cuts18177.take 2).map (fun c => (2386427905-1+2*2^9*c.k,98779631520337+c.lower,98780011148437+c.upper)) = pointBounds18177 := by
 decide +kernel
def cuts18178 : List PrefixCut := [⟨24,133391408,133391491⟩,
⟨97,541341288,541341621⟩,
⟨128,716712170,716712610⟩]
theorem checked18178 : checkPrefixCuts (2^48) 2386558977 9 Manual.Count131072.C018178.packed 128 cuts18178 = true := by
 decide +kernel
def pointBounds18178 : List (Nat × Nat × Nat) := [(2386583552,98780474940405,98780854569023),(2386658304,98780882890285,98781262519153)]
theorem point_links_checked18178 : (cuts18178.take 2).map (fun c => (2386558977-1+2*2^9*c.k,98780341548997+c.lower,98780721177532+c.upper)) = pointBounds18178 := by
 decide +kernel
def cuts18179 : List PrefixCut := [⟨42,230561334,230561480⟩,
⟨115,639429124,639429515⟩,
⟨128,710422441,710422877⟩]
theorem checked18179 : checkPrefixCuts (2^48) 2386690049 9 Manual.Count131072.C018179.packed 128 cuts18179 = true := by
 decide +kernel
def pointBounds18179 : List (Nat × Nat × Nat) := [(2386733056,98781288822501,98781668451622),(2386807808,98781697690291,98782077319657)]
theorem point_links_checked18179 : (cuts18179.take 2).map (fun c => (2386690049-1+2*2^9*c.k,98781058261167+c.lower,98781437890142+c.upper)) = pointBounds18179 := by
 decide +kernel
def cuts18180 : List PrefixCut := [⟨60,340220151,340220361⟩,
⟨128,717930706,717931148⟩]
theorem checked18180 : checkPrefixCuts (2^48) 2386821121 9 Manual.Count131072.C018180.packed 128 cuts18180 = true := by
 decide +kernel
def pointBounds18180 : List (Nat × Nat × Nat) := [(2386882560,98782108903759,98782488533380)]
theorem point_links_checked18180 : (cuts18180.take 1).map (fun c => (2386821121-1+2*2^9*c.k,98781768683608+c.lower,98782148313019+c.upper)) = pointBounds18180 := by
 decide +kernel
def cuts18181 : List PrefixCut := [⟨5,27593787,27593804⟩,
⟨78,433710990,433711256⟩,
⟨128,720839083,720839523⟩]
theorem checked18181 : checkPrefixCuts (2^48) 2386952193 9 Manual.Count131072.C018181.packed 128 cuts18181 = true := by
 decide +kernel
def pointBounds18181 : List (Nat × Nat × Nat) := [(2386957312,98782514208101,98782893837971),(2387032064,98782920325304,98783299955423)]
theorem point_links_checked18181 : (cuts18181.take 2).map (fun c => (2386952193-1+2*2^9*c.k,98782486614314+c.lower,98782866244167+c.upper)) = pointBounds18181 := by
 decide +kernel
def cuts18182 : List PrefixCut := [⟨23,128055964,128056043⟩,
⟨96,542401626,542401957⟩,
⟨128,722804151,722804594⟩]
theorem checked18182 : checkPrefixCuts (2^48) 2387083265 9 Manual.Count131072.C018182.packed 128 cuts18182 = true := by
 decide +kernel
def pointBounds18182 : List (Nat × Nat × Nat) := [(2387106816,98783335509361,98783715139733),(2387181568,98783749855023,98784129485647)]
theorem point_links_checked18182 : (cuts18182.take 2).map (fun c => (2387083265-1+2*2^9*c.k,98783207453397+c.lower,98783587083690+c.upper)) = pointBounds18182 := by
 decide +kernel
def cuts18183 : List PrefixCut := [⟨41,225322771,225322910⟩,
⟨114,638345489,638345882⟩,
⟨128,713567756,713568194⟩]
theorem checked18183 : checkPrefixCuts (2^48) 2387214337 9 Manual.Count131072.C018183.packed 128 cuts18183 = true := by
 decide +kernel
def pointBounds18183 : List (Nat × Nat × Nat) := [(2387256320,98784155580319,98784535211194),(2387331072,98784568603037,98784948234166)]
theorem point_links_checked18183 : (cuts18183.take 2).map (fun c => (2387214337-1+2*2^9*c.k,98783930257548+c.lower,98784309888284+c.upper)) = pointBounds18183 := by
 decide +kernel
def cuts18184 : List PrefixCut := [⟨59,322224533,322224734⟩,
⟨128,701267133,701267565⟩]
theorem checked18184 : checkPrefixCuts (2^48) 2387345409 9 Manual.Count131072.C018184.packed 128 cuts18184 = true := by
 decide +kernel
def pointBounds18184 : List (Nat × Nat × Nat) := [(2387405824,98784966049837,98785345681212)]
theorem point_links_checked18184 : (cuts18184.take 1).map (fun c => (2387345409-1+2*2^9*c.k,98784643825304+c.lower,98785023456478+c.upper)) = pointBounds18184 := by
 decide +kernel
def cuts18185 : List PrefixCut := [⟨4,20867646,20867659⟩,
⟨77,438213642,438213906⟩,
⟨128,725750314,725750752⟩]
theorem checked18185 : checkPrefixCuts (2^48) 2387476481 9 Manual.Count131072.C018185.packed 128 cuts18185 = true := by
 decide +kernel
def pointBounds18185 : List (Nat × Nat × Nat) := [(2387480576,98785365960083,98785745591702),(2387555328,98785783306079,98786162937949)]
theorem point_links_checked18185 : (cuts18185.take 2).map (fun c => (2387476481-1+2*2^9*c.k,98785345092437+c.lower,98785724724043+c.upper)) = pointBounds18185 := by
 decide +kernel
def cuts18186 : List PrefixCut := [⟨22,126141615,126141693⟩,
⟨95,539689139,539689470⟩,
⟨128,724767496,724767943⟩]
theorem checked18186 : checkPrefixCuts (2^48) 2387607553 9 Manual.Count131072.C018186.packed 128 cuts18186 = true := by
 decide +kernel
def pointBounds18186 : List (Nat × Nat × Nat) := [(2387630080,98786196984366,98786576616488),(2387704832,98786610531890,98786990164265)]
theorem point_links_checked18186 : (cuts18186.take 2).map (fun c => (2387607553-1+2*2^9*c.k,98786070842751+c.lower,98786450474795+c.upper)) = pointBounds18186 := by
 decide +kernel
def cuts18187 : List PrefixCut := [⟨40,222208397,222208531⟩,
⟨113,633372339,633372721⟩,
⟨128,717065266,717065698⟩]
theorem checked18187 : checkPrefixCuts (2^48) 2387738625 9 Manual.Count131072.C018187.packed 128 cuts18187 = true := by
 decide +kernel
def pointBounds18187 : List (Nat × Nat × Nat) := [(2387779584,98787017818644,98787397451269),(2387854336,98787428982586,98787808615459)]
theorem point_links_checked18187 : (cuts18187.take 2).map (fun c => (2387738625-1+2*2^9*c.k,98786795610247+c.lower,98787175242738+c.upper)) = pointBounds18187 := by
 decide +kernel
def cuts18188 : List PrefixCut := [⟨58,321800217,321800416⟩,
⟨128,719029819,719030258⟩]
theorem checked18188 : checkPrefixCuts (2^48) 2387869697 9 Manual.Count131072.C018188.packed 128 cuts18188 = true := by
 decide +kernel
def pointBounds18188 : List (Nat × Nat × Nat) := [(2387929088,98787834475730,98788214108852)]
theorem point_links_checked18188 : (cuts18188.take 1).map (fun c => (2387869697-1+2*2^9*c.k,98787512675513+c.lower,98787892308436+c.upper)) = pointBounds18188 := by
 decide +kernel
def cuts18189 : List PrefixCut := [⟨3,17798436,17798448⟩,
⟨76,418551454,418551714⟩,
⟨128,706142897,706143331⟩]
theorem checked18189 : checkPrefixCuts (2^48) 2388000769 9 Manual.Count131072.C018189.packed 128 cuts18189 = true := by
 decide +kernel
def pointBounds18189 : List (Nat × Nat × Nat) := [(2388003840,98788249503768,98788629137142),(2388078592,98788650256786,98789029890408)]
theorem point_links_checked18189 : (cuts18189.take 2).map (fun c => (2388000769-1+2*2^9*c.k,98788231705332+c.lower,98788611338694+c.upper)) = pointBounds18189 := by
 decide +kernel
def cuts18190 : List PrefixCut := [⟨21,110555976,110556044⟩,
⟨94,515644745,515645057⟩,
⟨128,703982552,703982982⟩]
theorem checked18190 : checkPrefixCuts (2^48) 2388131841 9 Manual.Count131072.C018190.packed 128 cuts18190 = true := by
 decide +kernel
def pointBounds18190 : List (Nat × Nat × Nat) := [(2388153344,98789048404205,98789428038069),(2388228096,98789453492974,98789833127082)]
theorem point_links_checked18190 : (cuts18190.take 2).map (fun c => (2388131841-1+2*2^9*c.k,98788937848229+c.lower,98789317482025+c.upper)) = pointBounds18190 := by
 decide +kernel
def cuts18191 : List PrefixCut := [⟨39,220038251,220038383⟩,
⟨112,626751631,626752008⟩,
⟨128,715493829,715494262⟩]
theorem checked18191 : checkPrefixCuts (2^48) 2388262913 9 Manual.Count131072.C018191.packed 128 cuts18191 = true := by
 decide +kernel
def pointBounds18191 : List (Nat × Nat × Nat) := [(2388302848,98789861869032,98790241503390),(2388377600,98790268582412,98790648217015)]
theorem point_links_checked18191 : (cuts18191.take 2).map (fun c => (2388262913-1+2*2^9*c.k,98789641830781+c.lower,98790021465007+c.upper)) = pointBounds18191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000255
