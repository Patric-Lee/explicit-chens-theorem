import PlattAssemblyKernel
import PlattCertificates.Count131072.C019152
import PlattCertificates.Count131072.C019153
import PlattCertificates.Count131072.C019154
import PlattCertificates.Count131072.C019155
import PlattCertificates.Count131072.C019156
import PlattCertificates.Count131072.C019157
import PlattCertificates.Count131072.C019158
import PlattCertificates.Count131072.C019159
import PlattCertificates.Count131072.C019160
import PlattCertificates.Count131072.C019161
import PlattCertificates.Count131072.C019162
import PlattCertificates.Count131072.C019163
import PlattCertificates.Count131072.C019164
import PlattCertificates.Count131072.C019165
import PlattCertificates.Count131072.C019166
import PlattCertificates.Count131072.C019167
import PlattCertificates.Count131072.C019168
import PlattCertificates.Count131072.C019169
import PlattCertificates.Count131072.C019170
import PlattCertificates.Count131072.C019171
import PlattCertificates.Count131072.C019172
import PlattCertificates.Count131072.C019173
import PlattCertificates.Count131072.C019174
import PlattCertificates.Count131072.C019175
import PlattCertificates.Count131072.C019176
import PlattCertificates.Count131072.C019177
import PlattCertificates.Count131072.C019178
import PlattCertificates.Count131072.C019179
import PlattCertificates.Count131072.C019180
import PlattCertificates.Count131072.C019181
import PlattCertificates.Count131072.C019182
import PlattCertificates.Count131072.C019183
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000286
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19152 : List PrefixCut := [⟨73,387575612,387575849⟩,
⟨128,676738417,676738824⟩]
theorem checked19152 : checkPrefixCuts (2^48) 2514223105 9 Manual.Count131072.C019152.packed 128 cuts19152 = true := by
 decide +kernel
def pointBounds19152 : List (Nat × Nat × Nat) := [(2514297856,99459150771709,99459530808844)]
theorem point_links_checked19152 : (cuts19152.take 1).map (fun c => (2514223105-1+2*2^9*c.k,99458763196097+c.lower,99459143232995+c.upper)) = pointBounds19152 := by
 decide +kernel
def cuts19153 : List PrefixCut := [⟨22,116088719,116088788⟩,
⟨99,527708403,527708719⟩,
⟨128,684203335,684203745⟩]
theorem checked19153 : checkPrefixCuts (2^48) 2514354177 9 Manual.Count131072.C019153.packed 128 cuts19153 = true := by
 decide +kernel
def pointBounds19153 : List (Nat × Nat × Nat) := [(2514376704,99459556023233,99459936060607),(2514455552,99459967642917,99460347680538)]
theorem point_links_checked19153 : (cuts19153.take 2).map (fun c => (2514354177-1+2*2^9*c.k,99459439934514+c.lower,99459819971819+c.upper)) = pointBounds19153 := by
 decide +kernel
def cuts19154 : List PrefixCut := [⟨48,258134258,258134410⟩,
⟨125,665586483,665586880⟩,
⟨128,680697788,680698194⟩]
theorem checked19154 : checkPrefixCuts (2^48) 2514485249 9 Manual.Count131072.C019154.packed 128 cuts19154 = true := by
 decide +kernel
def pointBounds19154 : List (Nat × Nat × Nat) := [(2514534400,99460382272107,99460762309974),(2514613248,99460789724332,99461169762444)]
theorem point_links_checked19154 : (cuts19154.take 2).map (fun c => (2514485249-1+2*2^9*c.k,99460124137849+c.lower,99460504175564+c.upper)) = pointBounds19154 := by
 decide +kernel
def cuts19155 : List PrefixCut := [⟨74,396245802,396246040⟩,
⟨128,686146853,686147260⟩]
theorem checked19155 : checkPrefixCuts (2^48) 2514616321 9 Manual.Count131072.C019155.packed 128 cuts19155 = true := by
 decide +kernel
def pointBounds19155 : List (Nat × Nat × Nat) := [(2514692096,99461201081439,99461581119798)]
theorem point_links_checked19155 : (cuts19155.take 1).map (fun c => (2514616321-1+2*2^9*c.k,99460804835637+c.lower,99461184873758+c.upper)) = pointBounds19155 := by
 decide +kernel
def cuts19156 : List PrefixCut := [⟨23,116742131,116742200⟩,
⟨100,529192759,529193078⟩,
⟨128,677380781,677381185⟩]
theorem checked19156 : checkPrefixCuts (2^48) 2514747393 9 Manual.Count131072.C019156.packed 128 cuts19156 = true := by
 decide +kernel
def pointBounds19156 : List (Nat × Nat × Nat) := [(2514770944,99461607724621,99461987763218),(2514849792,99462020175249,99462400214096)]
theorem point_links_checked19156 : (cuts19156.take 2).map (fun c => (2514747393-1+2*2^9*c.k,99461490982490+c.lower,99461871021018+c.upper)) = pointBounds19156 := by
 decide +kernel
def cuts19157 : List PrefixCut := [⟨49,254064630,254064785⟩,
⟨126,661788717,661789110⟩,
⟨128,670742163,670742561⟩]
theorem checked19157 : checkPrefixCuts (2^48) 2514878465 9 Manual.Count131072.C019157.packed 128 cuts19157 = true := by
 decide +kernel
def pointBounds19157 : List (Nat × Nat × Nat) := [(2514928640,99462422427901,99462802466988),(2515007488,99462830151988,99463210191313)]
theorem point_links_checked19157 : (cuts19157.take 2).map (fun c => (2514878465-1+2*2^9*c.k,99462168363271+c.lower,99462548402203+c.upper)) = pointBounds19157 := by
 decide +kernel
def cuts19158 : List PrefixCut := [⟨75,403682161,403682399⟩,
⟨128,684696752,684697160⟩]
theorem checked19158 : checkPrefixCuts (2^48) 2515009537 9 Manual.Count131072.C019158.packed 128 cuts19158 = true := by
 decide +kernel
def pointBounds19158 : List (Nat × Nat × Nat) := [(2515086336,99463242787595,99463622827163)]
theorem point_links_checked19158 : (cuts19158.take 1).map (fun c => (2515009537-1+2*2^9*c.k,99462839105434+c.lower,99463219144764+c.upper)) = pointBounds19158 := by
 decide +kernel
def cuts19159 : List PrefixCut := [⟨24,127019711,127019785⟩,
⟨101,540300956,540301275⟩,
⟨128,680296584,680296985⟩]
theorem checked19159 : checkPrefixCuts (2^48) 2515140609 9 Manual.Count131072.C019159.packed 128 cuts19159 = true := by
 decide +kernel
def pointBounds19159 : List (Nat × Nat × Nat) := [(2515165184,99463650821897,99464030861709),(2515244032,99464064103142,99464444143199)]
theorem point_links_checked19159 : (cuts19159.take 2).map (fun c => (2515140609-1+2*2^9*c.k,99463523802186+c.lower,99463903841924+c.upper)) = pointBounds19159 := by
 decide +kernel
def cuts19160 : List PrefixCut := [⟨50,262193893,262194045⟩,
⟨127,671085000,671085406⟩,
⟨128,676680028,676680437⟩]
theorem checked19160 : checkPrefixCuts (2^48) 2515271681 9 Manual.Count131072.C019160.packed 128 cuts19160 = true := by
 decide +kernel
def pointBounds19160 : List (Nat × Nat × Nat) := [(2515322880,99464466292663,99464846332954),(2515401728,99464875183770,99465255224315)]
theorem point_links_checked19160 : (cuts19160.take 2).map (fun c => (2515271681-1+2*2^9*c.k,99464204098770+c.lower,99464584138909+c.upper)) = pointBounds19160 := by
 decide +kernel
def cuts19161 : List PrefixCut := [⟨76,393883769,393883999⟩,
⟨128,671497398,671497791⟩]
theorem checked19161 : checkPrefixCuts (2^48) 2515402753 9 Manual.Count131072.C019161.packed 128 cuts19161 = true := by
 decide +kernel
def pointBounds19161 : List (Nat × Nat × Nat) := [(2515480576,99465274662567,99465654703345)]
theorem point_links_checked19161 : (cuts19161.take 1).map (fun c => (2515402753-1+2*2^9*c.k,99464880778798+c.lower,99465260819346+c.upper)) = pointBounds19161 := by
 decide +kernel
def cuts19162 : List PrefixCut := [⟨25,128678251,128678329⟩,
⟨102,540775740,540776067⟩,
⟨128,675490649,675491056⟩]
theorem checked19162 : checkPrefixCuts (2^48) 2515533825 9 Manual.Count131072.C019162.packed 128 cuts19162 = true := by
 decide +kernel
def pointBounds19162 : List (Nat × Nat × Nat) := [(2515559424,99465680954447,99466060995466),(2515638272,99466093051936,99466473093204)]
theorem point_links_checked19162 : (cuts19162.take 2).map (fun c => (2515533825-1+2*2^9*c.k,99465552276196+c.lower,99465932317137+c.upper)) = pointBounds19162 := by
 decide +kernel
def cuts19163 : List PrefixCut := [⟨51,272334682,272334845⟩,
⟨128,674336739,674337140⟩]
theorem checked19163 : checkPrefixCuts (2^48) 2515664897 9 Manual.Count131072.C019163.packed 128 cuts19163 = true := by
 decide +kernel
def pointBounds19163 : List (Nat × Nat × Nat) := [(2515717120,99466500101527,99466880143038),(2515795968,99466902103584,99467282145333)]
theorem point_links_checked19163 : (cuts19163.take 2).map (fun c => (2515664897-1+2*2^9*c.k,99466227766845+c.lower,99466607808193+c.upper)) = pointBounds19163 := by
 decide +kernel
def cuts19164 : List PrefixCut := [⟨77,409038058,409038305⟩,
⟨128,681685613,681686024⟩]
theorem checked19164 : checkPrefixCuts (2^48) 2515795969 9 Manual.Count131072.C019164.packed 128 cuts19164 = true := by
 decide +kernel
def pointBounds19164 : List (Nat × Nat × Nat) := [(2515874816,99467311141642,99467691183638)]
theorem point_links_checked19164 : (cuts19164.take 1).map (fun c => (2515795969-1+2*2^9*c.k,99466902103584+c.lower,99467282145333+c.upper)) = pointBounds19164 := by
 decide +kernel
def cuts19165 : List PrefixCut := [⟨26,134923207,134923288⟩,
⟨103,538565556,538565877⟩,
⟨128,674042483,674042883⟩]
theorem checked19165 : checkPrefixCuts (2^48) 2515927041 9 Manual.Count131072.C019165.packed 128 cuts19165 = true := by
 decide +kernel
def pointBounds19165 : List (Nat × Nat × Nat) := [(2515953664,99467718712404,99468098754645),(2516032512,99468122354753,99468502397234)]
theorem point_links_checked19165 : (cuts19165.take 2).map (fun c => (2515927041-1+2*2^9*c.k,99467583789197+c.lower,99467963831357+c.upper)) = pointBounds19165 := by
 decide +kernel
def cuts19166 : List PrefixCut := [⟨52,280570481,280570651⟩,
⟨128,687655482,687655891⟩]
theorem checked19166 : checkPrefixCuts (2^48) 2516058113 9 Manual.Count131072.C019166.packed 128 cuts19166 = true := by
 decide +kernel
def pointBounds19166 : List (Nat × Nat × Nat) := [(2516111360,99468538402161,99468918444891)]
theorem point_links_checked19166 : (cuts19166.take 1).map (fun c => (2516058113-1+2*2^9*c.k,99468257831680+c.lower,99468637874240+c.upper)) = pointBounds19166 := by
 decide +kernel
def cuts19167 : List PrefixCut := [⟨1,4922083,4922086⟩,
⟨78,411434927,411435178⟩,
⟨128,671735148,671735553⟩]
theorem checked19167 : checkPrefixCuts (2^48) 2516189185 9 Manual.Count131072.C019167.packed 128 cuts19167 = true := by
 decide +kernel
def pointBounds19167 : List (Nat × Nat × Nat) := [(2516190208,99468950409245,99469330452217),(2516269056,99469356922089,99469736965309)]
theorem point_links_checked19167 : (cuts19167.take 2).map (fun c => (2516189185-1+2*2^9*c.k,99468945487162+c.lower,99469325530131+c.upper)) = pointBounds19167 := by
 decide +kernel
def cuts19168 : List PrefixCut := [⟨27,142732224,142732309⟩,
⟨104,549443387,549443722⟩,
⟨128,677740436,677740847⟩]
theorem checked19168 : checkPrefixCuts (2^48) 2516320257 9 Manual.Count131072.C019168.packed 128 cuts19168 = true := by
 decide +kernel
def pointBounds19168 : List (Nat × Nat × Nat) := [(2516347904,99469759954534,99470139997993),(2516426752,99470166665697,99470546709406)]
theorem point_links_checked19168 : (cuts19168.take 2).map (fun c => (2516320257-1+2*2^9*c.k,99469617222310+c.lower,99469997265684+c.upper)) = pointBounds19168 := by
 decide +kernel
def cuts19169 : List PrefixCut := [⟨53,280638403,280638574⟩,
⟨128,673231173,673231580⟩]
theorem checked19169 : checkPrefixCuts (2^48) 2516451329 9 Manual.Count131072.C019169.packed 128 cuts19169 = true := by
 decide +kernel
def pointBounds19169 : List (Nat × Nat × Nat) := [(2516505600,99470575601149,99470955645105)]
theorem point_links_checked19169 : (cuts19169.take 1).map (fun c => (2516451329-1+2*2^9*c.k,99470294962746+c.lower,99470675006531+c.upper)) = pointBounds19169 := by
 decide +kernel
def cuts19170 : List PrefixCut := [⟨2,8612298,8612304⟩,
⟨79,409916548,409916791⟩,
⟨128,666149716,666150108⟩]
theorem checked19170 : checkPrefixCuts (2^48) 2516582401 9 Manual.Count131072.C019170.packed 128 cuts19170 = true := by
 decide +kernel
def pointBounds19170 : List (Nat × Nat × Nat) := [(2516584448,99470976806217,99471356850415),(2516663296,99471378110467,99471758154902)]
theorem point_links_checked19170 : (cuts19170.take 2).map (fun c => (2516582401-1+2*2^9*c.k,99470968193919+c.lower,99471348238111+c.upper)) = pointBounds19170 := by
 decide +kernel
def cuts19171 : List PrefixCut := [⟨28,148190131,148190221⟩,
⟨105,550028390,550028720⟩,
⟨128,677410675,677411079⟩]
theorem checked19171 : checkPrefixCuts (2^48) 2516713473 9 Manual.Count131072.C019171.packed 128 cuts19171 = true := by
 decide +kernel
def pointBounds19171 : List (Nat × Nat × Nat) := [(2516742144,99471782533766,99472162578440),(2516820992,99472184372025,99472564416939)]
theorem point_links_checked19171 : (cuts19171.take 2).map (fun c => (2516713473-1+2*2^9*c.k,99471634343635+c.lower,99472014388219+c.upper)) = pointBounds19171 := by
 decide +kernel
def cuts19172 : List PrefixCut := [⟨54,288534833,288535006⟩,
⟨128,683302778,683303192⟩]
theorem checked19172 : checkPrefixCuts (2^48) 2516844545 9 Manual.Count131072.C019172.packed 128 cuts19172 = true := by
 decide +kernel
def pointBounds19172 : List (Nat × Nat × Nat) := [(2516899840,99472600289143,99472980334304)]
theorem point_links_checked19172 : (cuts19172.take 1).map (fun c => (2516844545-1+2*2^9*c.k,99472311754310+c.lower,99472691799298+c.upper)) = pointBounds19172 := by
 decide +kernel
def cuts19173 : List PrefixCut := [⟨3,14537968,14537977⟩,
⟨80,424949322,424949572⟩,
⟨128,679129524,679129923⟩]
theorem checked19173 : checkPrefixCuts (2^48) 2516975617 9 Manual.Count131072.C019173.packed 128 cuts19173 = true := by
 decide +kernel
def pointBounds19173 : List (Nat × Nat × Nat) := [(2516978688,99473009595056,99473389640467),(2517057536,99473420006410,99473800052062)]
theorem point_links_checked19173 : (cuts19173.take 2).map (fun c => (2516975617-1+2*2^9*c.k,99472995057088+c.lower,99473375102490+c.upper)) = pointBounds19173 := by
 decide +kernel
def cuts19174 : List PrefixCut := [⟨29,155435522,155435614⟩,
⟨106,559447367,559447700⟩,
⟨128,677752345,677752746⟩]
theorem checked19174 : checkPrefixCuts (2^48) 2517106689 9 Manual.Count131072.C019174.packed 128 cuts19174 = true := by
 decide +kernel
def pointBounds19174 : List (Nat × Nat × Nat) := [(2517136384,99473829622134,99474209668027),(2517215232,99474233633979,99474613680113)]
theorem point_links_checked19174 : (cuts19174.take 2).map (fun c => (2517106689-1+2*2^9*c.k,99473674186612+c.lower,99474054232413+c.upper)) = pointBounds19174 := by
 decide +kernel
def cuts19175 : List PrefixCut := [⟨55,290278737,290278910⟩,
⟨128,672908982,672909384⟩]
theorem checked19175 : checkPrefixCuts (2^48) 2517237761 9 Manual.Count131072.C019175.packed 128 cuts19175 = true := by
 decide +kernel
def pointBounds19175 : List (Nat × Nat × Nat) := [(2517294080,99474642217694,99475022264069)]
theorem point_links_checked19175 : (cuts19175.take 1).map (fun c => (2517237761-1+2*2^9*c.k,99474351938957+c.lower,99474731985159+c.upper)) = pointBounds19175 := by
 decide +kernel
def cuts19176 : List PrefixCut := [⟨4,20126348,20126359⟩,
⟨81,430138005,430138256⟩,
⟨128,678128968,678129370⟩]
theorem checked19176 : checkPrefixCuts (2^48) 2517368833 9 Manual.Count131072.C019176.packed 128 cuts19176 = true := by
 decide +kernel
def pointBounds19176 : List (Nat × Nat × Nat) := [(2517372928,99475044974287,99475425020902),(2517451776,99475454985944,99475835032799)]
theorem point_links_checked19176 : (cuts19176.take 2).map (fun c => (2517368833-1+2*2^9*c.k,99475024847939+c.lower,99475404894543+c.upper)) = pointBounds19176 := by
 decide +kernel
def cuts19177 : List PrefixCut := [⟨30,157311925,157312020⟩,
⟨107,568974977,568975320⟩,
⟨128,680441538,680441944⟩]
theorem checked19177 : checkPrefixCuts (2^48) 2517499905 9 Manual.Count131072.C019177.packed 128 cuts19177 = true := by
 decide +kernel
def pointBounds19177 : List (Nat × Nat × Nat) := [(2517530624,99475860288832,99476240335933),(2517609472,99476271951884,99476651999233)]
theorem point_links_checked19177 : (cuts19177.take 2).map (fun c => (2517499905-1+2*2^9*c.k,99475702976907+c.lower,99476083023913+c.upper)) = pointBounds19177 := by
 decide +kernel
def cuts19178 : List PrefixCut := [⟨56,298506563,298506740⟩,
⟨128,679399956,679400360⟩]
theorem checked19178 : checkPrefixCuts (2^48) 2517630977 9 Manual.Count131072.C019178.packed 128 cuts19178 = true := by
 decide +kernel
def pointBounds19178 : List (Nat × Nat × Nat) := [(2517688320,99476681925008,99477061972597)]
theorem point_links_checked19178 : (cuts19178.take 1).map (fun c => (2517630977-1+2*2^9*c.k,99476383418445+c.lower,99476763465857+c.upper)) = pointBounds19178 := by
 decide +kernel
def cuts19179 : List PrefixCut := [⟨5,28619660,28619677⟩,
⟨82,439014245,439014507⟩,
⟨128,682494801,682495206⟩]
theorem checked19179 : checkPrefixCuts (2^48) 2517762049 9 Manual.Count131072.C019179.packed 128 cuts19179 = true := by
 decide +kernel
def pointBounds19179 : List (Nat × Nat × Nat) := [(2517767168,99477091438061,99477471485894),(2517846016,99477501832646,99477881880724)]
theorem point_links_checked19179 : (cuts19179.take 2).map (fun c => (2517762049-1+2*2^9*c.k,99477062818401+c.lower,99477442866217+c.upper)) = pointBounds19179 := by
 decide +kernel
def cuts19180 : List PrefixCut := [⟨31,164218289,164218387⟩,
⟨108,572351487,572351826⟩,
⟨128,675528570,675528972⟩]
theorem checked19180 : checkPrefixCuts (2^48) 2517893121 9 Manual.Count131072.C019180.packed 128 cuts19180 = true := by
 decide +kernel
def pointBounds19180 : List (Nat × Nat × Nat) := [(2517924864,99477909531491,99478289579810),(2518003712,99478317664689,99478697713249)]
theorem point_links_checked19180 : (cuts19180.take 2).map (fun c => (2517893121-1+2*2^9*c.k,99477745313202+c.lower,99478125361423+c.upper)) = pointBounds19180 := by
 decide +kernel
def cuts19181 : List PrefixCut := [⟨57,302819433,302819608⟩,
⟨128,678064290,678064688⟩]
theorem checked19181 : checkPrefixCuts (2^48) 2518024193 9 Manual.Count131072.C019181.packed 128 cuts19181 = true := by
 decide +kernel
def pointBounds19181 : List (Nat × Nat × Nat) := [(2518082560,99478723661205,99479103710003)]
theorem point_links_checked19181 : (cuts19181.take 1).map (fun c => (2518024193-1+2*2^9*c.k,99478420841772+c.lower,99478800890395+c.upper)) = pointBounds19181 := by
 decide +kernel
def cuts19182 : List PrefixCut := [⟨6,31856752,31856770⟩,
⟨83,436710120,436710382⟩,
⟨128,677358250,677358653⟩]
theorem checked19182 : checkPrefixCuts (2^48) 2518155265 9 Manual.Count131072.C019182.packed 128 cuts19182 = true := by
 decide +kernel
def pointBounds19182 : List (Nat × Nat × Nat) := [(2518161408,99479130762814,99479510811853),(2518240256,99479535616182,99479915665465)]
theorem point_links_checked19182 : (cuts19182.take 2).map (fun c => (2518155265-1+2*2^9*c.k,99479098906062+c.lower,99479478955083+c.upper)) = pointBounds19182 := by
 decide +kernel
def cuts19183 : List PrefixCut := [⟨32,174699122,174699226⟩,
⟨109,584668536,584668886⟩,
⟨128,683470569,683470978⟩]
theorem checked19183 : checkPrefixCuts (2^48) 2518286337 9 Manual.Count131072.C019183.packed 128 cuts19183 = true := by
 decide +kernel
def pointBounds19183 : List (Nat × Nat × Nat) := [(2518319104,99479950963434,99480331012962),(2518397952,99480360932848,99480740982622)]
theorem point_links_checked19183 : (cuts19183.take 2).map (fun c => (2518286337-1+2*2^9*c.k,99479776264312+c.lower,99480156313736+c.upper)) = pointBounds19183 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000286
