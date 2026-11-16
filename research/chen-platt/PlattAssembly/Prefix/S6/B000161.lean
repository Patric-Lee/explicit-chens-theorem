import PlattAssemblyKernel
import PlattCertificates.Count131072.C055152
import PlattCertificates.Count131072.C055153
import PlattCertificates.Count131072.C055154
import PlattCertificates.Count131072.C055155
import PlattCertificates.Count131072.C055156
import PlattCertificates.Count131072.C055157
import PlattCertificates.Count131072.C055158
import PlattCertificates.Count131072.C055159
import PlattCertificates.Count131072.C055160
import PlattCertificates.Count131072.C055161
import PlattCertificates.Count131072.C055162
import PlattCertificates.Count131072.C055163
import PlattCertificates.Count131072.C055164
import PlattCertificates.Count131072.C055165
import PlattCertificates.Count131072.C055166
import PlattCertificates.Count131072.C055167
import PlattCertificates.Count131072.C055168
import PlattCertificates.Count131072.C055169
import PlattCertificates.Count131072.C055170
import PlattCertificates.Count131072.C055171
import PlattCertificates.Count131072.C055172
import PlattCertificates.Count131072.C055173
import PlattCertificates.Count131072.C055174
import PlattCertificates.Count131072.C055175
import PlattCertificates.Count131072.C055176
import PlattCertificates.Count131072.C055177
import PlattCertificates.Count131072.C055178
import PlattCertificates.Count131072.C055179
import PlattCertificates.Count131072.C055180
import PlattCertificates.Count131072.C055181
import PlattCertificates.Count131072.C055182
import PlattCertificates.Count131072.C055183
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000161
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55152 : List PrefixCut := [⟨64,224506500,224506626⟩]
theorem checked55152 : checkPrefixCuts (2^48) 7232815105 10 Manual.Count131072.C055152.packed 64 cuts55152 = true := by
 decide +kernel
def cuts55153 : List PrefixCut := [⟨16,57750716,57750749⟩,
⟨64,226876282,226876411⟩]
theorem checked55153 : checkPrefixCuts (2^48) 7232946177 10 Manual.Count131072.C055153.packed 64 cuts55153 = true := by
 decide +kernel
def pointBounds55153 : List (Nat × Nat × Nat) := [(7232978944,112874982140478,112875369954684)]
theorem point_links_checked55153 : (cuts55153.take 1).map (fun c => (7232946177-1+2*2^10*c.k,112874924389762+c.lower,112875312203935+c.upper)) = pointBounds55153 := by
 decide +kernel
def cuts55154 : List PrefixCut := [⟨63,220373426,220373553⟩,
⟨64,223953538,223953667⟩]
theorem checked55154 : checkPrefixCuts (2^48) 7233077249 10 Manual.Count131072.C055154.packed 64 cuts55154 = true := by
 decide +kernel
def pointBounds55154 : List (Nat × Nat × Nat) := [(7233206272,112875371639470,112875759453899)]
theorem point_links_checked55154 : (cuts55154.take 1).map (fun c => (7233077249-1+2*2^10*c.k,112875151266044+c.lower,112875539080346+c.upper)) = pointBounds55154 := by
 decide +kernel
def cuts55155 : List PrefixCut := [⟨64,224338645,224338767⟩]
theorem checked55155 : checkPrefixCuts (2^48) 7233208321 10 Manual.Count131072.C055155.packed 64 cuts55155 = true := by
 decide +kernel
def cuts55156 : List PrefixCut := [⟨46,162034946,162035036⟩,
⟨64,223283916,223284040⟩]
theorem checked55156 : checkPrefixCuts (2^48) 7233339393 10 Manual.Count131072.C055156.packed 64 cuts55156 = true := by
 decide +kernel
def pointBounds55156 : List (Nat × Nat × Nat) := [(7233433600,112875761593173,112876149407816)]
theorem point_links_checked55156 : (cuts55156.take 1).map (fun c => (7233339393-1+2*2^10*c.k,112875599558227+c.lower,112875987372780+c.upper)) = pointBounds55156 := by
 decide +kernel
def cuts55157 : List PrefixCut := [⟨64,221256433,221256559⟩]
theorem checked55157 : checkPrefixCuts (2^48) 7233470465 10 Manual.Count131072.C055157.packed 64 cuts55157 = true := by
 decide +kernel
def cuts55158 : List PrefixCut := [⟨29,100120520,100120578⟩,
⟨64,220201792,220201920⟩]
theorem checked55158 : checkPrefixCuts (2^48) 7233601537 10 Manual.Count131072.C055158.packed 64 cuts55158 = true := by
 decide +kernel
def pointBounds55158 : List (Nat × Nat × Nat) := [(7233660928,112876144219096,112876532033957)]
theorem point_links_checked55158 : (cuts55158.take 1).map (fun c => (7233601537-1+2*2^10*c.k,112876044098576+c.lower,112876431913379+c.upper)) = pointBounds55158 := by
 decide +kernel
def cuts55159 : List PrefixCut := [⟨64,223505251,223505376⟩]
theorem checked55159 : checkPrefixCuts (2^48) 7233732609 10 Manual.Count131072.C055159.packed 64 cuts55159 = true := by
 decide +kernel
def cuts55160 : List PrefixCut := [⟨12,41634407,41634431⟩,
⟨64,224084848,224084979⟩]
theorem checked55160 : checkPrefixCuts (2^48) 7233863681 10 Manual.Count131072.C055160.packed 64 cuts55160 = true := by
 decide +kernel
def pointBounds55160 : List (Nat × Nat × Nat) := [(7233888256,112876529440026,112876917255106)]
theorem point_links_checked55160 : (cuts55160.take 1).map (fun c => (7233863681-1+2*2^10*c.k,112876487805619+c.lower,112876875620675+c.upper)) = pointBounds55160 := by
 decide +kernel
def cuts55161 : List PrefixCut := [⟨59,209878919,209879037⟩,
⟨64,225909569,225909696⟩]
theorem checked55161 : checkPrefixCuts (2^48) 7233994753 10 Manual.Count131072.C055161.packed 64 cuts55161 = true := by
 decide +kernel
def pointBounds55161 : List (Nat × Nat × Nat) := [(7234115584,112876921769386,112877309584691)]
theorem point_links_checked55161 : (cuts55161.take 1).map (fun c => (7233994753-1+2*2^10*c.k,112876711890467+c.lower,112877099705654+c.upper)) = pointBounds55161 := by
 decide +kernel
def cuts55162 : List PrefixCut := [⟨64,223998898,223999026⟩]
theorem checked55162 : checkPrefixCuts (2^48) 7234125825 10 Manual.Count131072.C055162.packed 64 cuts55162 = true := by
 decide +kernel
def cuts55163 : List PrefixCut := [⟨42,150925590,150925676⟩,
⟨64,229130725,229130855⟩]
theorem checked55163 : checkPrefixCuts (2^48) 7234256897 10 Manual.Count131072.C055163.packed 64 cuts55163 = true := by
 decide +kernel
def pointBounds55163 : List (Nat × Nat × Nat) := [(7234342912,112877312724524,112877700540052)]
theorem point_links_checked55163 : (cuts55163.take 1).map (fun c => (7234256897-1+2*2^10*c.k,112877161798934+c.lower,112877549614376+c.upper)) = pointBounds55163 := by
 decide +kernel
def cuts55164 : List PrefixCut := [⟨64,223796268,223796397⟩]
theorem checked55164 : checkPrefixCuts (2^48) 7234387969 10 Manual.Count131072.C055164.packed 64 cuts55164 = true := by
 decide +kernel
def cuts55165 : List PrefixCut := [⟨25,88863735,88863783⟩,
⟨64,226710219,226710346⟩]
theorem checked55165 : checkPrefixCuts (2^48) 7234519041 10 Manual.Count131072.C055165.packed 64 cuts55165 = true := by
 decide +kernel
def pointBounds55165 : List (Nat × Nat × Nat) := [(7234570240,112877703589662,112878091405411)]
theorem point_links_checked55165 : (cuts55165.take 1).map (fun c => (7234519041-1+2*2^10*c.k,112877614725927+c.lower,112878002541628+c.upper)) = pointBounds55165 := by
 decide +kernel
def cuts55166 : List PrefixCut := [⟨64,226161445,226161571⟩]
theorem checked55166 : checkPrefixCuts (2^48) 7234650113 10 Manual.Count131072.C055166.packed 64 cuts55166 = true := by
 decide +kernel
def cuts55167 : List PrefixCut := [⟨8,28868065,28868081⟩,
⟨64,224367676,224367806⟩]
theorem checked55167 : checkPrefixCuts (2^48) 7234781185 10 Manual.Count131072.C055167.packed 64 cuts55167 = true := by
 decide +kernel
def pointBounds55167 : List (Nat × Nat × Nat) := [(7234797568,112878096465656,112878484281626)]
theorem point_links_checked55167 : (cuts55167.take 1).map (fun c => (7234781185-1+2*2^10*c.k,112878067597591+c.lower,112878455413545+c.upper)) = pointBounds55167 := by
 decide +kernel
def cuts55168 : List PrefixCut := [⟨55,191294818,191294927⟩,
⟨64,224519203,224519330⟩]
theorem checked55168 : checkPrefixCuts (2^48) 7234912257 10 Manual.Count131072.C055168.packed 64 cuts55168 = true := by
 decide +kernel
def pointBounds55168 : List (Nat × Nat × Nat) := [(7235024896,112878483260085,112878871076278)]
theorem point_links_checked55168 : (cuts55168.take 1).map (fun c => (7234912257-1+2*2^10*c.k,112878291965267+c.lower,112878679781351+c.upper)) = pointBounds55168 := by
 decide +kernel
def cuts55169 : List PrefixCut := [⟨64,227510773,227510902⟩]
theorem checked55169 : checkPrefixCuts (2^48) 7235043329 10 Manual.Count131072.C055169.packed 64 cuts55169 = true := by
 decide +kernel
def cuts55170 : List PrefixCut := [⟨38,133283287,133283363⟩,
⟨64,226028315,226028444⟩]
theorem checked55170 : checkPrefixCuts (2^48) 7235174401 10 Manual.Count131072.C055170.packed 64 cuts55170 = true := by
 decide +kernel
def pointBounds55170 : List (Nat × Nat × Nat) := [(7235252224,112878877278530,112879265094946)]
theorem point_links_checked55170 : (cuts55170.take 1).map (fun c => (7235174401-1+2*2^10*c.k,112878743995243+c.lower,112879131811583+c.upper)) = pointBounds55170 := by
 decide +kernel
def cuts55171 : List PrefixCut := [⟨64,221861627,221861751⟩]
theorem checked55171 : checkPrefixCuts (2^48) 7235305473 10 Manual.Count131072.C055171.packed 64 cuts55171 = true := by
 decide +kernel
def cuts55172 : List PrefixCut := [⟨21,73369461,73369504⟩,
⟨64,221235212,221235339⟩]
theorem checked55172 : checkPrefixCuts (2^48) 7235436545 10 Manual.Count131072.C055172.packed 64 cuts55172 = true := by
 decide +kernel
def pointBounds55172 : List (Nat × Nat × Nat) := [(7235479552,112879265254646,112879653071282)]
theorem point_links_checked55172 : (cuts55172.take 1).map (fun c => (7235436545-1+2*2^10*c.k,112879191885185+c.lower,112879579701778+c.upper)) = pointBounds55172 := by
 decide +kernel
def cuts55173 : List PrefixCut := [⟨64,227961107,227961239⟩]
theorem checked55173 : checkPrefixCuts (2^48) 7235567617 10 Manual.Count131072.C055173.packed 64 cuts55173 = true := by
 decide +kernel
def cuts55174 : List PrefixCut := [⟨4,14043203,14043211⟩,
⟨64,222044089,222044216⟩]
theorem checked55174 : checkPrefixCuts (2^48) 7235698689 10 Manual.Count131072.C055174.packed 64 cuts55174 = true := by
 decide +kernel
def pointBounds55174 : List (Nat × Nat × Nat) := [(7235706880,112879655124707,112880042941567)]
theorem point_links_checked55174 : (cuts55174.take 1).map (fun c => (7235698689-1+2*2^10*c.k,112879641081504+c.lower,112880028898356+c.upper)) = pointBounds55174 := by
 decide +kernel
def cuts55175 : List PrefixCut := [⟨51,177539039,177539142⟩,
⟨64,224918655,224918786⟩]
theorem checked55175 : checkPrefixCuts (2^48) 7235829761 10 Manual.Count131072.C055175.packed 64 cuts55175 = true := by
 decide +kernel
def pointBounds55175 : List (Nat × Nat × Nat) := [(7235934208,112880040664632,112880428481714)]
theorem point_links_checked55175 : (cuts55175.take 1).map (fun c => (7235829761-1+2*2^10*c.k,112879863125593+c.lower,112880250942572+c.upper)) = pointBounds55175 := by
 decide +kernel
def cuts55176 : List PrefixCut := [⟨64,224875685,224875814⟩]
theorem checked55176 : checkPrefixCuts (2^48) 7235960833 10 Manual.Count131072.C055176.packed 64 cuts55176 = true := by
 decide +kernel
def cuts55177 : List PrefixCut := [⟨34,118134923,118134989⟩,
⟨64,225844048,225844175⟩]
theorem checked55177 : checkPrefixCuts (2^48) 7236091905 10 Manual.Count131072.C055177.packed 64 cuts55177 = true := by
 decide +kernel
def pointBounds55177 : List (Nat × Nat × Nat) := [(7236161536,112880431054856,112880818872161)]
theorem point_links_checked55177 : (cuts55177.take 1).map (fun c => (7236091905-1+2*2^10*c.k,112880312919933+c.lower,112880700737172+c.upper)) = pointBounds55177 := by
 decide +kernel
def cuts55178 : List PrefixCut := [⟨64,227668183,227668310⟩]
theorem checked55178 : checkPrefixCuts (2^48) 7236222977 10 Manual.Count131072.C055178.packed 64 cuts55178 = true := by
 decide +kernel
def cuts55179 : List PrefixCut := [⟨17,59434989,59435023⟩,
⟨64,223268695,223268820⟩]
theorem checked55179 : checkPrefixCuts (2^48) 7236354049 10 Manual.Count131072.C055179.packed 64 cuts55179 = true := by
 decide +kernel
def pointBounds55179 : List (Nat × Nat × Nat) := [(7236388864,112880825867153,112881213684680)]
theorem point_links_checked55179 : (cuts55179.take 1).map (fun c => (7236354049-1+2*2^10*c.k,112880766432164+c.lower,112881154249657+c.upper)) = pointBounds55179 := by
 decide +kernel
def cuts55180 : List PrefixCut := [⟨64,225520625,225520753⟩]
theorem checked55180 : checkPrefixCuts (2^48) 7236485121 10 Manual.Count131072.C055180.packed 64 cuts55180 = true := by
 decide +kernel
def pointBounds55180 : List (Nat × Nat × Nat) := [(7236616192,112881215221484,112881603039230)]
theorem point_links_checked55180 : (cuts55180.take 1).map (fun c => (7236485121-1+2*2^10*c.k,112880989700859+c.lower,112881377518477+c.upper)) = pointBounds55180 := by
 decide +kernel
def cuts55181 : List PrefixCut := [⟨64,225827711,225827840⟩]
theorem checked55181 : checkPrefixCuts (2^48) 7236616193 10 Manual.Count131072.C055181.packed 64 cuts55181 = true := by
 decide +kernel
def cuts55182 : List PrefixCut := [⟨47,166003711,166003807⟩,
⟨64,222517583,222517713⟩]
theorem checked55182 : checkPrefixCuts (2^48) 7236747265 10 Manual.Count131072.C055182.packed 64 cuts55182 = true := by
 decide +kernel
def pointBounds55182 : List (Nat × Nat × Nat) := [(7236843520,112881607052906,112881994870877)]
theorem point_links_checked55182 : (cuts55182.take 1).map (fun c => (7236747265-1+2*2^10*c.k,112881441049195+c.lower,112881828867070+c.upper)) = pointBounds55182 := by
 decide +kernel
def cuts55183 : List PrefixCut := [⟨64,223913715,223913839⟩]
theorem checked55183 : checkPrefixCuts (2^48) 7236878337 10 Manual.Count131072.C055183.packed 64 cuts55183 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000161
