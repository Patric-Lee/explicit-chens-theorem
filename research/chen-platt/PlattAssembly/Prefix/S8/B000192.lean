import PlattAssemblyKernel
import PlattCertificates.Count131072.C076144
import PlattCertificates.Count131072.C076145
import PlattCertificates.Count131072.C076146
import PlattCertificates.Count131072.C076147
import PlattCertificates.Count131072.C076148
import PlattCertificates.Count131072.C076149
import PlattCertificates.Count131072.C076150
import PlattCertificates.Count131072.C076151
import PlattCertificates.Count131072.C076152
import PlattCertificates.Count131072.C076153
import PlattCertificates.Count131072.C076154
import PlattCertificates.Count131072.C076155
import PlattCertificates.Count131072.C076156
import PlattCertificates.Count131072.C076157
import PlattCertificates.Count131072.C076158
import PlattCertificates.Count131072.C076159
import PlattCertificates.Count131072.C076160
import PlattCertificates.Count131072.C076161
import PlattCertificates.Count131072.C076162
import PlattCertificates.Count131072.C076163
import PlattCertificates.Count131072.C076164
import PlattCertificates.Count131072.C076165
import PlattCertificates.Count131072.C076166
import PlattCertificates.Count131072.C076167
import PlattCertificates.Count131072.C076168
import PlattCertificates.Count131072.C076169
import PlattCertificates.Count131072.C076170
import PlattCertificates.Count131072.C076171
import PlattCertificates.Count131072.C076172
import PlattCertificates.Count131072.C076173
import PlattCertificates.Count131072.C076174
import PlattCertificates.Count131072.C076175
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000192
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts76144 : List PrefixCut := [⟨64,161819937,161820036⟩]
theorem checked76144 : checkPrefixCuts (2^48) 9984278529 10 Manual.Count131072.C076144.packed 64 cuts76144 = true := by
 decide +kernel
def cuts76145 : List PrefixCut := [⟨64,161169401,161169502⟩]
theorem checked76145 : checkPrefixCuts (2^48) 9984409601 10 Manual.Count131072.C076145.packed 64 cuts76145 = true := by
 decide +kernel
def cuts76146 : List PrefixCut := [⟨20,49475228,49475256⟩,
⟨64,159955077,159955173⟩]
theorem checked76146 : checkPrefixCuts (2^48) 9984540673 10 Manual.Count131072.C076146.packed 64 cuts76146 = true := by
 decide +kernel
def pointBounds76146 : List (Nat × Nat × Nat) := [(9984581632,116844144132411,116844534251300)]
theorem point_links_checked76146 : (cuts76146.take 1).map (fun c => (9984540673-1+2*2^10*c.k,116844094657183+c.lower,116844484776044+c.upper)) = pointBounds76146 := by
 decide +kernel
def cuts76147 : List PrefixCut := [⟨64,160657744,160657838⟩]
theorem checked76147 : checkPrefixCuts (2^48) 9984671745 10 Manual.Count131072.C076147.packed 64 cuts76147 = true := by
 decide +kernel
def cuts76148 : List PrefixCut := [⟨45,110928441,110928508⟩,
⟨64,158484996,158485091⟩]
theorem checked76148 : checkPrefixCuts (2^48) 9984802817 10 Manual.Count131072.C076148.packed 64 cuts76148 = true := by
 decide +kernel
def pointBounds76148 : List (Nat × Nat × Nat) := [(9984894976,116844526198445,116844916317563)]
theorem point_links_checked76148 : (cuts76148.take 1).map (fun c => (9984802817-1+2*2^10*c.k,116844415270004+c.lower,116844805389055+c.upper)) = pointBounds76148 := by
 decide +kernel
def cuts76149 : List PrefixCut := [⟨64,160879040,160879138⟩]
theorem checked76149 : checkPrefixCuts (2^48) 9984933889 10 Manual.Count131072.C076149.packed 64 cuts76149 = true := by
 decide +kernel
def cuts76150 : List PrefixCut := [⟨64,161412523,161412630⟩]
theorem checked76150 : checkPrefixCuts (2^48) 9985064961 10 Manual.Count131072.C076150.packed 64 cuts76150 = true := by
 decide +kernel
def cuts76151 : List PrefixCut := [⟨6,14573819,14573827⟩,
⟨64,159324423,159324519⟩]
theorem checked76151 : checkPrefixCuts (2^48) 9985196033 10 Manual.Count131072.C076151.packed 64 cuts76151 = true := by
 decide +kernel
def pointBounds76151 : List (Nat × Nat × Nat) := [(9985208320,116844910620382,116845300739741)]
theorem point_links_checked76151 : (cuts76151.take 1).map (fun c => (9985196033-1+2*2^10*c.k,116844896046563+c.lower,116845286165914+c.upper)) = pointBounds76151 := by
 decide +kernel
def cuts76152 : List PrefixCut := [⟨64,160759955,160760055⟩]
theorem checked76152 : checkPrefixCuts (2^48) 9985327105 10 Manual.Count131072.C076152.packed 64 cuts76152 = true := by
 decide +kernel
def cuts76153 : List PrefixCut := [⟨31,78420103,78420152⟩,
⟨64,162505519,162505621⟩]
theorem checked76153 : checkPrefixCuts (2^48) 9985458177 10 Manual.Count131072.C076153.packed 64 cuts76153 = true := by
 decide +kernel
def pointBounds76153 : List (Nat × Nat × Nat) := [(9985521664,116845294551044,116845684670640)]
theorem point_links_checked76153 : (cuts76153.take 1).map (fun c => (9985458177-1+2*2^10*c.k,116845216130941+c.lower,116845606250488+c.upper)) = pointBounds76153 := by
 decide +kernel
def cuts76154 : List PrefixCut := [⟨64,159571849,159571946⟩]
theorem checked76154 : checkPrefixCuts (2^48) 9985589249 10 Manual.Count131072.C076154.packed 64 cuts76154 = true := by
 decide +kernel
def cuts76155 : List PrefixCut := [⟨56,140515083,140515168⟩,
⟨64,160866383,160866478⟩]
theorem checked76155 : checkPrefixCuts (2^48) 9985720321 10 Manual.Count131072.C076155.packed 64 cuts76155 = true := by
 decide +kernel
def pointBounds76155 : List (Nat × Nat × Nat) := [(9985835008,116845678723392,116846068843223)]
theorem point_links_checked76155 : (cuts76155.take 1).map (fun c => (9985720321-1+2*2^10*c.k,116845538208309+c.lower,116845928328055+c.upper)) = pointBounds76155 := by
 decide +kernel
def cuts76156 : List PrefixCut := [⟨64,159116670,159116764⟩]
theorem checked76156 : checkPrefixCuts (2^48) 9985851393 10 Manual.Count131072.C076156.packed 64 cuts76156 = true := by
 decide +kernel
def cuts76157 : List PrefixCut := [⟨64,162637928,162638030⟩]
theorem checked76157 : checkPrefixCuts (2^48) 9985982465 10 Manual.Count131072.C076157.packed 64 cuts76157 = true := by
 decide +kernel
def cuts76158 : List PrefixCut := [⟨17,42899975,42900004⟩,
⟨64,158492386,158492483⟩]
theorem checked76158 : checkPrefixCuts (2^48) 9986113537 10 Manual.Count131072.C076158.packed 64 cuts76158 = true := by
 decide +kernel
def pointBounds76158 : List (Nat × Nat × Nat) := [(9986148352,116846063729265,116846453849331)]
theorem point_links_checked76158 : (cuts76158.take 1).map (fun c => (9986113537-1+2*2^10*c.k,116846020829290+c.lower,116846410949327+c.upper)) = pointBounds76158 := by
 decide +kernel
def cuts76159 : List PrefixCut := [⟨64,158264826,158264914⟩]
theorem checked76159 : checkPrefixCuts (2^48) 9986244609 10 Manual.Count131072.C076159.packed 64 cuts76159 = true := by
 decide +kernel
def cuts76160 : List PrefixCut := [⟨42,105612080,105612137⟩,
⟨64,160996747,160996840⟩]
theorem checked76160 : checkPrefixCuts (2^48) 9986375681 10 Manual.Count131072.C076160.packed 64 cuts76160 = true := by
 decide +kernel
def pointBounds76160 : List (Nat × Nat × Nat) := [(9986461696,116846443198582,116846833318861)]
theorem point_links_checked76160 : (cuts76160.take 1).map (fun c => (9986375681-1+2*2^10*c.k,116846337586502+c.lower,116846727706724+c.upper)) = pointBounds76160 := by
 decide +kernel
def cuts76161 : List PrefixCut := [⟨64,161276489,161276591⟩]
theorem checked76161 : checkPrefixCuts (2^48) 9986506753 10 Manual.Count131072.C076161.packed 64 cuts76161 = true := by
 decide +kernel
def cuts76162 : List PrefixCut := [⟨64,163078204,163078305⟩]
theorem checked76162 : checkPrefixCuts (2^48) 9986637825 10 Manual.Count131072.C076162.packed 64 cuts76162 = true := by
 decide +kernel
def cuts76163 : List PrefixCut := [⟨3,7299856,7299860⟩,
⟨64,158932940,158933032⟩]
theorem checked76163 : checkPrefixCuts (2^48) 9986768897 10 Manual.Count131072.C076163.packed 64 cuts76163 = true := by
 decide +kernel
def pointBounds76163 : List (Nat × Nat × Nat) := [(9986775040,116846830237798,116847220358320)]
theorem point_links_checked76163 : (cuts76163.take 1).map (fun c => (9986768897-1+2*2^10*c.k,116846822937942+c.lower,116847213058460+c.upper)) = pointBounds76163 := by
 decide +kernel
def cuts76164 : List PrefixCut := [⟨64,162453866,162453958⟩]
theorem checked76164 : checkPrefixCuts (2^48) 9986899969 10 Manual.Count131072.C076164.packed 64 cuts76164 = true := by
 decide +kernel
def cuts76165 : List PrefixCut := [⟨28,69755300,69755342⟩,
⟨64,158787846,158787943⟩]
theorem checked76165 : checkPrefixCuts (2^48) 9987031041 10 Manual.Count131072.C076165.packed 64 cuts76165 = true := by
 decide +kernel
def pointBounds76165 : List (Nat × Nat × Nat) := [(9987088384,116847214080048,116847604200792)]
theorem point_links_checked76165 : (cuts76165.take 1).map (fun c => (9987031041-1+2*2^10*c.k,116847144324748+c.lower,116847534445450+c.upper)) = pointBounds76165 := by
 decide +kernel
def cuts76166 : List PrefixCut := [⟨64,159433978,159434078⟩]
theorem checked76166 : checkPrefixCuts (2^48) 9987162113 10 Manual.Count131072.C076166.packed 64 cuts76166 = true := by
 decide +kernel
def cuts76167 : List PrefixCut := [⟨53,132150786,132150864⟩,
⟨64,159600991,159601086⟩]
theorem checked76167 : checkPrefixCuts (2^48) 9987293185 10 Manual.Count131072.C076167.packed 64 cuts76167 = true := by
 decide +kernel
def pointBounds76167 : List (Nat × Nat × Nat) := [(9987401728,116847594697358,116847984818335)]
theorem point_links_checked76167 : (cuts76167.take 1).map (fun c => (9987293185-1+2*2^10*c.k,116847462546572+c.lower,116847852667471+c.upper)) = pointBounds76167 := by
 decide +kernel
def cuts76168 : List PrefixCut := [⟨64,163995397,163995498⟩]
theorem checked76168 : checkPrefixCuts (2^48) 9987424257 10 Manual.Count131072.C076168.packed 64 cuts76168 = true := by
 decide +kernel
def cuts76169 : List PrefixCut := [⟨64,159371348,159371446⟩]
theorem checked76169 : checkPrefixCuts (2^48) 9987555329 10 Manual.Count131072.C076169.packed 64 cuts76169 = true := by
 decide +kernel
def cuts76170 : List PrefixCut := [⟨14,35227690,35227711⟩,
⟨64,162948358,162948462⟩]
theorem checked76170 : checkPrefixCuts (2^48) 9987686401 10 Manual.Count131072.C076170.packed 64 cuts76170 = true := by
 decide +kernel
def pointBounds76170 : List (Nat × Nat × Nat) := [(9987715072,116847980741998,116848370863212)]
theorem point_links_checked76170 : (cuts76170.take 1).map (fun c => (9987686401-1+2*2^10*c.k,116847945514308+c.lower,116848335635501+c.upper)) = pointBounds76170 := by
 decide +kernel
def cuts76171 : List PrefixCut := [⟨64,160128069,160128162⟩]
theorem checked76171 : checkPrefixCuts (2^48) 9987817473 10 Manual.Count131072.C076171.packed 64 cuts76171 = true := by
 decide +kernel
def cuts76172 : List PrefixCut := [⟨39,98747408,98747472⟩,
⟨64,162324097,162324196⟩]
theorem checked76172 : checkPrefixCuts (2^48) 9987948545 10 Manual.Count131072.C076172.packed 64 cuts76172 = true := by
 decide +kernel
def pointBounds76172 : List (Nat × Nat × Nat) := [(9988028416,116848367338143,116848757459597)]
theorem point_links_checked76172 : (cuts76172.take 1).map (fun c => (9987948545-1+2*2^10*c.k,116848268590735+c.lower,116848658712125+c.upper)) = pointBounds76172 := by
 decide +kernel
def cuts76173 : List PrefixCut := [⟨64,161842900,161842997⟩]
theorem checked76173 : checkPrefixCuts (2^48) 9988079617 10 Manual.Count131072.C076173.packed 64 cuts76173 = true := by
 decide +kernel
def cuts76174 : List PrefixCut := [⟨64,159445415,159445519⟩]
theorem checked76174 : checkPrefixCuts (2^48) 9988210689 10 Manual.Count131072.C076174.packed 64 cuts76174 = true := by
 decide +kernel
def pointBounds76174 : List (Nat × Nat × Nat) := [(9988341760,116848752203147,116849142324837)]
theorem point_links_checked76174 : (cuts76174.take 1).map (fun c => (9988210689-1+2*2^10*c.k,116848592757732+c.lower,116848982879318+c.upper)) = pointBounds76174 := by
 decide +kernel
def cuts76175 : List PrefixCut := [⟨64,158485197,158485301⟩]
theorem checked76175 : checkPrefixCuts (2^48) 9988341761 10 Manual.Count131072.C076175.packed 64 cuts76175 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000192
