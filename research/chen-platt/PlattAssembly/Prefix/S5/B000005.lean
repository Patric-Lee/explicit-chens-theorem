import PlattAssemblyKernel
import PlattCertificates.Count131072.C040160
import PlattCertificates.Count131072.C040161
import PlattCertificates.Count131072.C040162
import PlattCertificates.Count131072.C040163
import PlattCertificates.Count131072.C040164
import PlattCertificates.Count131072.C040165
import PlattCertificates.Count131072.C040166
import PlattCertificates.Count131072.C040167
import PlattCertificates.Count131072.C040168
import PlattCertificates.Count131072.C040169
import PlattCertificates.Count131072.C040170
import PlattCertificates.Count131072.C040171
import PlattCertificates.Count131072.C040172
import PlattCertificates.Count131072.C040173
import PlattCertificates.Count131072.C040174
import PlattCertificates.Count131072.C040175
import PlattCertificates.Count131072.C040176
import PlattCertificates.Count131072.C040177
import PlattCertificates.Count131072.C040178
import PlattCertificates.Count131072.C040179
import PlattCertificates.Count131072.C040180
import PlattCertificates.Count131072.C040181
import PlattCertificates.Count131072.C040182
import PlattCertificates.Count131072.C040183
import PlattCertificates.Count131072.C040184
import PlattCertificates.Count131072.C040185
import PlattCertificates.Count131072.C040186
import PlattCertificates.Count131072.C040187
import PlattCertificates.Count131072.C040188
import PlattCertificates.Count131072.C040189
import PlattCertificates.Count131072.C040190
import PlattCertificates.Count131072.C040191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40160 : List PrefixCut := [⟨64,314718047,314718233⟩]
theorem checked40160 : checkPrefixCuts (2^48) 5267783681 10 Manual.Count131072.C040160.packed 64 cuts40160 = true := by
 decide +kernel
def cuts40161 : List PrefixCut := [⟨10,48516103,48516133⟩,
⟨64,310489128,310489317⟩]
theorem checked40161 : checkPrefixCuts (2^48) 5267914753 10 Manual.Count131072.C040161.packed 64 cuts40161 = true := by
 decide +kernel
def pointBounds40161 : List (Nat × Nat × Nat) := [(5267935232,108916767854461,108917153390068)]
theorem point_links_checked40161 : (cuts40161.take 1).map (fun c => (5267914753-1+2*2^10*c.k,108916719338358+c.lower,108917104873935+c.upper)) = pointBounds40161 := by
 decide +kernel
def cuts40162 : List PrefixCut := [⟨27,133308665,133308743⟩,
⟨64,313473493,313473682⟩]
theorem checked40162 : checkPrefixCuts (2^48) 5268045825 10 Manual.Count131072.C040162.packed 64 cuts40162 = true := by
 decide +kernel
def pointBounds40162 : List (Nat × Nat × Nat) := [(5268101120,108917163136151,108917548671995)]
theorem point_links_checked40162 : (cuts40162.take 1).map (fun c => (5268045825-1+2*2^10*c.k,108917029827486+c.lower,108917415363252+c.upper)) = pointBounds40162 := by
 decide +kernel
def cuts40163 : List PrefixCut := [⟨44,213929000,213929129⟩,
⟨64,311969664,311969853⟩]
theorem checked40163 : checkPrefixCuts (2^48) 5268176897 10 Manual.Count131072.C040163.packed 64 cuts40163 = true := by
 decide +kernel
def pointBounds40163 : List (Nat × Nat × Nat) := [(5268267008,108917557229979,108917942766063)]
theorem point_links_checked40163 : (cuts40163.take 1).map (fun c => (5268176897-1+2*2^10*c.k,108917343300979+c.lower,108917728836934+c.upper)) = pointBounds40163 := by
 decide +kernel
def cuts40164 : List PrefixCut := [⟨61,296735311,296735489⟩,
⟨64,312549600,312549787⟩]
theorem checked40164 : checkPrefixCuts (2^48) 5268307969 10 Manual.Count131072.C040164.packed 64 cuts40164 = true := by
 decide +kernel
def pointBounds40164 : List (Nat × Nat × Nat) := [(5268432896,108917952005954,108918337542276)]
theorem point_links_checked40164 : (cuts40164.take 1).map (fun c => (5268307969-1+2*2^10*c.k,108917655270643+c.lower,108918040806787+c.upper)) = pointBounds40164 := by
 decide +kernel
def cuts40165 : List PrefixCut := [⟨64,314945999,314946185⟩]
theorem checked40165 : checkPrefixCuts (2^48) 5268439041 10 Manual.Count131072.C040165.packed 64 cuts40165 = true := by
 decide +kernel
def cuts40166 : List PrefixCut := [⟨14,68971864,68971904⟩,
⟨64,315312140,315312326⟩]
theorem checked40166 : checkPrefixCuts (2^48) 5268570113 10 Manual.Count131072.C040166.packed 64 cuts40166 = true := by
 decide +kernel
def pointBounds40166 : List (Nat × Nat × Nat) := [(5268598784,108918351738106,108918737274663)]
theorem point_links_checked40166 : (cuts40166.take 1).map (fun c => (5268570113-1+2*2^10*c.k,108918282766242+c.lower,108918668302759+c.upper)) = pointBounds40166 := by
 decide +kernel
def cuts40167 : List PrefixCut := [⟨31,152684764,152684854⟩,
⟨64,312098911,312099096⟩]
theorem checked40167 : checkPrefixCuts (2^48) 5268701185 10 Manual.Count131072.C040167.packed 64 cuts40167 = true := by
 decide +kernel
def pointBounds40167 : List (Nat × Nat × Nat) := [(5268764672,108918750763146,108919136299939)]
theorem point_links_checked40167 : (cuts40167.take 1).map (fun c => (5268701185-1+2*2^10*c.k,108918598078382+c.lower,108918983615085+c.upper)) = pointBounds40167 := by
 decide +kernel
def cuts40168 : List PrefixCut := [⟨48,235057404,235057543⟩,
⟨64,313533545,313533730⟩]
theorem checked40168 : checkPrefixCuts (2^48) 5268832257 10 Manual.Count131072.C040168.packed 64 cuts40168 = true := by
 decide +kernel
def pointBounds40168 : List (Nat × Nat × Nat) := [(5268930560,108919145234697,108919530771724)]
theorem point_links_checked40168 : (cuts40168.take 1).map (fun c => (5268832257-1+2*2^10*c.k,108918910177293+c.lower,108919295714181+c.upper)) = pointBounds40168 := by
 decide +kernel
def cuts40169 : List PrefixCut := [⟨64,312564132,312564317⟩]
theorem checked40169 : checkPrefixCuts (2^48) 5268963329 10 Manual.Count131072.C040169.packed 64 cuts40169 = true := by
 decide +kernel
def cuts40170 : List PrefixCut := [⟨1,5288577,5288580⟩,
⟨64,315814963,315815149⟩]
theorem checked40170 : checkPrefixCuts (2^48) 5269094401 10 Manual.Count131072.C040170.packed 64 cuts40170 = true := by
 decide +kernel
def pointBounds40170 : List (Nat × Nat × Nat) := [(5269096448,108919541563547,108919927100808)]
theorem point_links_checked40170 : (cuts40170.take 1).map (fun c => (5269094401-1+2*2^10*c.k,108919536274970+c.lower,108919921812228+c.upper)) = pointBounds40170 := by
 decide +kernel
def cuts40171 : List PrefixCut := [⟨18,89689595,89689646⟩,
⟨64,312334965,312335150⟩]
theorem checked40171 : checkPrefixCuts (2^48) 5269225473 10 Manual.Count131072.C040171.packed 64 cuts40171 = true := by
 decide +kernel
def pointBounds40171 : List (Nat × Nat × Nat) := [(5269262336,108919941779528,108920327317023)]
theorem point_links_checked40171 : (cuts40171.take 1).map (fun c => (5269225473-1+2*2^10*c.k,108919852089933+c.lower,108920237627377+c.upper)) = pointBounds40171 := by
 decide +kernel
def cuts40172 : List PrefixCut := [⟨35,171308176,171308280⟩,
⟨64,308908529,308908717⟩]
theorem checked40172 : checkPrefixCuts (2^48) 5269356545 10 Manual.Count131072.C040172.packed 64 cuts40172 = true := by
 decide +kernel
def pointBounds40172 : List (Nat × Nat × Nat) := [(5269428224,108920335733074,108920721270807)]
theorem point_links_checked40172 : (cuts40172.take 1).map (fun c => (5269356545-1+2*2^10*c.k,108920164424898+c.lower,108920549962527+c.upper)) = pointBounds40172 := by
 decide +kernel
def cuts40173 : List PrefixCut := [⟨52,258156898,258157049⟩,
⟨64,314883404,314883589⟩]
theorem checked40173 : checkPrefixCuts (2^48) 5269487617 10 Manual.Count131072.C040173.packed 64 cuts40173 = true := by
 decide +kernel
def pointBounds40173 : List (Nat × Nat × Nat) := [(5269594112,108920731490325,108921117028293)]
theorem point_links_checked40173 : (cuts40173.take 1).map (fun c => (5269487617-1+2*2^10*c.k,108920473333427+c.lower,108920858871244+c.upper)) = pointBounds40173 := by
 decide +kernel
def cuts40174 : List PrefixCut := [⟨64,311083133,311083323⟩]
theorem checked40174 : checkPrefixCuts (2^48) 5269618689 10 Manual.Count131072.C040174.packed 64 cuts40174 = true := by
 decide +kernel
def cuts40175 : List PrefixCut := [⟨5,24356455,24356470⟩,
⟨64,311556095,311556282⟩]
theorem checked40175 : checkPrefixCuts (2^48) 5269749761 10 Manual.Count131072.C040175.packed 64 cuts40175 = true := by
 decide +kernel
def pointBounds40175 : List (Nat × Nat × Nat) := [(5269760000,108921123656419,108921509194626)]
theorem point_links_checked40175 : (cuts40175.take 1).map (fun c => (5269749761-1+2*2^10*c.k,108921099299964+c.lower,108921484838156+c.upper)) = pointBounds40175 := by
 decide +kernel
def cuts40176 : List PrefixCut := [⟨22,107731554,107731616⟩,
⟨64,311815383,311815567⟩]
theorem checked40176 : checkPrefixCuts (2^48) 5269880833 10 Manual.Count131072.C040176.packed 64 cuts40176 = true := by
 decide +kernel
def pointBounds40176 : List (Nat × Nat × Nat) := [(5269925888,108921518587613,108921904126054)]
theorem point_links_checked40176 : (cuts40176.take 1).map (fun c => (5269880833-1+2*2^10*c.k,108921410856059+c.lower,108921796394438+c.upper)) = pointBounds40176 := by
 decide +kernel
def cuts40177 : List PrefixCut := [⟨39,190247392,190247501⟩,
⟨64,311914468,311914649⟩]
theorem checked40177 : checkPrefixCuts (2^48) 5270011905 10 Manual.Count131072.C040177.packed 64 cuts40177 = true := by
 decide +kernel
def pointBounds40177 : List (Nat × Nat × Nat) := [(5270091776,108921912918834,108922298457506)]
theorem point_links_checked40177 : (cuts40177.take 1).map (fun c => (5270011905-1+2*2^10*c.k,108921722671442+c.lower,108922108210005+c.upper)) = pointBounds40177 := by
 decide +kernel
def cuts40178 : List PrefixCut := [⟨56,273185840,273186002⟩,
⟨64,313348731,313348917⟩]
theorem checked40178 : checkPrefixCuts (2^48) 5270142977 10 Manual.Count131072.C040178.packed 64 cuts40178 = true := by
 decide +kernel
def pointBounds40178 : List (Nat × Nat × Nat) := [(5270257664,108922307771750,108922693310656)]
theorem point_links_checked40178 : (cuts40178.take 1).map (fun c => (5270142977-1+2*2^10*c.k,108922034585910+c.lower,108922420124654+c.upper)) = pointBounds40178 := by
 decide +kernel
def cuts40179 : List PrefixCut := [⟨64,314622713,314622899⟩]
theorem checked40179 : checkPrefixCuts (2^48) 5270274049 10 Manual.Count131072.C040179.packed 64 cuts40179 = true := by
 decide +kernel
def cuts40180 : List PrefixCut := [⟨9,43526378,43526404⟩,
⟨64,311036708,311036892⟩]
theorem checked40180 : checkPrefixCuts (2^48) 5270405121 10 Manual.Count131072.C040180.packed 64 cuts40180 = true := by
 decide +kernel
def pointBounds40180 : List (Nat × Nat × Nat) := [(5270423552,108922706083732,108923091622874)]
theorem point_links_checked40180 : (cuts40180.take 1).map (fun c => (5270405121-1+2*2^10*c.k,108922662557354+c.lower,108923048096470+c.upper)) = pointBounds40180 := by
 decide +kernel
def cuts40181 : List PrefixCut := [⟨26,126890499,126890577⟩,
⟨64,311936836,311937026⟩]
theorem checked40181 : checkPrefixCuts (2^48) 5270536193 10 Manual.Count131072.C040181.packed 64 cuts40181 = true := by
 decide +kernel
def pointBounds40181 : List (Nat × Nat × Nat) := [(5270589440,108923100484561,108923486023939)]
theorem point_links_checked40181 : (cuts40181.take 1).map (fun c => (5270536193-1+2*2^10*c.k,108922973594062+c.lower,108923359133362+c.upper)) = pointBounds40181 := by
 decide +kernel
def cuts40182 : List PrefixCut := [⟨43,209502279,209502402⟩,
⟨64,310433801,310433987⟩]
theorem checked40182 : checkPrefixCuts (2^48) 5270667265 10 Manual.Count131072.C040182.packed 64 cuts40182 = true := by
 decide +kernel
def pointBounds40182 : List (Nat × Nat × Nat) := [(5270755328,108923495033177,108923880572790)]
theorem point_links_checked40182 : (cuts40182.take 1).map (fun c => (5270667265-1+2*2^10*c.k,108923285530898+c.lower,108923671070388+c.upper)) = pointBounds40182 := by
 decide +kernel
def cuts40183 : List PrefixCut := [⟨60,294939726,294939901⟩,
⟨64,314004033,314004219⟩]
theorem checked40183 : checkPrefixCuts (2^48) 5270798337 10 Manual.Count131072.C040183.packed 64 cuts40183 = true := by
 decide +kernel
def pointBounds40183 : List (Nat × Nat × Nat) := [(5270921216,108923890904425,108924276444276)]
theorem point_links_checked40183 : (cuts40183.take 1).map (fun c => (5270798337-1+2*2^10*c.k,108923595964699+c.lower,108923981504375+c.upper)) = pointBounds40183 := by
 decide +kernel
def cuts40184 : List PrefixCut := [⟨64,308228891,308229080⟩]
theorem checked40184 : checkPrefixCuts (2^48) 5270929409 10 Manual.Count131072.C040184.packed 64 cuts40184 = true := by
 decide +kernel
def cuts40185 : List PrefixCut := [⟨13,62744895,62744933⟩,
⟨64,311959225,311959411⟩]
theorem checked40185 : checkPrefixCuts (2^48) 5271060481 10 Manual.Count131072.C040185.packed 64 cuts40185 = true := by
 decide +kernel
def pointBounds40185 : List (Nat × Nat × Nat) := [(5271087104,108924280942518,108924666482607)]
theorem point_links_checked40185 : (cuts40185.take 1).map (fun c => (5271060481-1+2*2^10*c.k,108924218197623+c.lower,108924603737674+c.upper)) = pointBounds40185 := by
 decide +kernel
def cuts40186 : List PrefixCut := [⟨30,144282511,144282598⟩,
⟨64,311737842,311738030⟩]
theorem checked40186 : checkPrefixCuts (2^48) 5271191553 10 Manual.Count131072.C040186.packed 64 cuts40186 = true := by
 decide +kernel
def pointBounds40186 : List (Nat × Nat × Nat) := [(5271252992,108924674439359,108925059979683)]
theorem point_links_checked40186 : (cuts40186.take 1).map (fun c => (5271191553-1+2*2^10*c.k,108924530156848+c.lower,108924915697085+c.upper)) = pointBounds40186 := by
 decide +kernel
def cuts40187 : List PrefixCut := [⟨47,232383337,232383475⟩,
⟨64,315841662,315841849⟩]
theorem checked40187 : checkPrefixCuts (2^48) 5271322625 10 Manual.Count131072.C040187.packed 64 cuts40187 = true := by
 decide +kernel
def pointBounds40187 : List (Nat × Nat × Nat) := [(5271418880,108925074278027,108925459818590)]
theorem point_links_checked40187 : (cuts40187.take 1).map (fun c => (5271322625-1+2*2^10*c.k,108924841894690+c.lower,108925227435115+c.upper)) = pointBounds40187 := by
 decide +kernel
def cuts40188 : List PrefixCut := [⟨64,315566835,315567028⟩]
theorem checked40188 : checkPrefixCuts (2^48) 5271453697 10 Manual.Count131072.C040188.packed 64 cuts40188 = true := by
 decide +kernel
def pointBounds40188 : List (Nat × Nat × Nat) := [(5271584768,108925473303187,108925858843992)]
theorem point_links_checked40188 : (cuts40188.take 1).map (fun c => (5271453697-1+2*2^10*c.k,108925157736352+c.lower,108925543276964+c.upper)) = pointBounds40188 := by
 decide +kernel
def cuts40189 : List PrefixCut := [⟨64,313636783,313636965⟩]
theorem checked40189 : checkPrefixCuts (2^48) 5271584769 10 Manual.Count131072.C040189.packed 64 cuts40189 = true := by
 decide +kernel
def cuts40190 : List PrefixCut := [⟨17,82492553,82492600⟩,
⟨64,308983862,308984045⟩]
theorem checked40190 : checkPrefixCuts (2^48) 5271715841 10 Manual.Count131072.C040190.packed 64 cuts40190 = true := by
 decide +kernel
def pointBounds40190 : List (Nat × Nat × Nat) := [(5271750656,108925869432523,108926254973557)]
theorem point_links_checked40190 : (cuts40190.take 1).map (fun c => (5271715841-1+2*2^10*c.k,108925786939970+c.lower,108926172480957+c.upper)) = pointBounds40190 := by
 decide +kernel
def cuts40191 : List PrefixCut := [⟨34,162951574,162951671⟩,
⟨64,309670234,309670418⟩]
theorem checked40191 : checkPrefixCuts (2^48) 5271846913 10 Manual.Count131072.C040191.packed 64 cuts40191 = true := by
 decide +kernel
def pointBounds40191 : List (Nat × Nat × Nat) := [(5271916544,108926258875406,108926644416673)]
theorem point_links_checked40191 : (cuts40191.take 1).map (fun c => (5271846913-1+2*2^10*c.k,108926095923832+c.lower,108926481465002+c.upper)) = pointBounds40191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000005
