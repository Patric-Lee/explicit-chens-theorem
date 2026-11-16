import PlattAssemblyKernel
import PlattCertificates.Count131072.C069184
import PlattCertificates.Count131072.C069185
import PlattCertificates.Count131072.C069186
import PlattCertificates.Count131072.C069187
import PlattCertificates.Count131072.C069188
import PlattCertificates.Count131072.C069189
import PlattCertificates.Count131072.C069190
import PlattCertificates.Count131072.C069191
import PlattCertificates.Count131072.C069192
import PlattCertificates.Count131072.C069193
import PlattCertificates.Count131072.C069194
import PlattCertificates.Count131072.C069195
import PlattCertificates.Count131072.C069196
import PlattCertificates.Count131072.C069197
import PlattCertificates.Count131072.C069198
import PlattCertificates.Count131072.C069199
import PlattCertificates.Count131072.C069200
import PlattCertificates.Count131072.C069201
import PlattCertificates.Count131072.C069202
import PlattCertificates.Count131072.C069203
import PlattCertificates.Count131072.C069204
import PlattCertificates.Count131072.C069205
import PlattCertificates.Count131072.C069206
import PlattCertificates.Count131072.C069207
import PlattCertificates.Count131072.C069208
import PlattCertificates.Count131072.C069209
import PlattCertificates.Count131072.C069210
import PlattCertificates.Count131072.C069211
import PlattCertificates.Count131072.C069212
import PlattCertificates.Count131072.C069213
import PlattCertificates.Count131072.C069214
import PlattCertificates.Count131072.C069215
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000287
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69184 : List PrefixCut := [⟨64,178185139,178185236⟩]
theorem checked69184 : checkPrefixCuts (2^48) 9072017409 10 Manual.Count131072.C069184.packed 64 cuts69184 = true := by
 decide +kernel
def cuts69185 : List PrefixCut := [⟨30,82715750,82715793⟩,
⟨64,176352031,176352129⟩]
theorem checked69185 : checkPrefixCuts (2^48) 9072148481 10 Manual.Count131072.C069185.packed 64 cuts69185 = true := by
 decide +kernel
def pointBounds69185 : List (Nat × Nat × Nat) := [(9072209920,115670172639894,115670562060681)]
theorem point_links_checked69185 : (cuts69185.take 1).map (fun c => (9072148481-1+2*2^10*c.k,115670089924144+c.lower,115670479344888+c.upper)) = pointBounds69185 := by
 decide +kernel
def cuts69186 : List PrefixCut := [⟨64,175046397,175046502⟩]
theorem checked69186 : checkPrefixCuts (2^48) 9072279553 10 Manual.Count131072.C069186.packed 64 cuts69186 = true := by
 decide +kernel
def cuts69187 : List PrefixCut := [⟨41,115196668,115196733⟩,
⟨64,177960248,177960347⟩]
theorem checked69187 : checkPrefixCuts (2^48) 9072410625 10 Manual.Count131072.C069187.packed 64 cuts69187 = true := by
 decide +kernel
def pointBounds69187 : List (Nat × Nat × Nat) := [(9072494592,115670556519240,115670945940252)]
theorem point_links_checked69187 : (cuts69187.take 1).map (fun c => (9072410625-1+2*2^10*c.k,115670441322572+c.lower,115670830743519+c.upper)) = pointBounds69187 := by
 decide +kernel
def cuts69188 : List PrefixCut := [⟨64,176623604,176623709⟩]
theorem checked69188 : checkPrefixCuts (2^48) 9072541697 10 Manual.Count131072.C069188.packed 64 cuts69188 = true := by
 decide +kernel
def cuts69189 : List PrefixCut := [⟨52,145441870,145441960⟩,
⟨64,177179491,177179599⟩]
theorem checked69189 : checkPrefixCuts (2^48) 9072672769 10 Manual.Count131072.C069189.packed 64 cuts69189 = true := by
 decide +kernel
def pointBounds69189 : List (Nat × Nat × Nat) := [(9072779264,115670941348294,115671330769535)]
theorem point_links_checked69189 : (cuts69189.take 1).map (fun c => (9072672769-1+2*2^10*c.k,115670795906424+c.lower,115671185327575+c.upper)) = pointBounds69189 := by
 decide +kernel
def cuts69190 : List PrefixCut := [⟨64,173174865,173174970⟩]
theorem checked69190 : checkPrefixCuts (2^48) 9072803841 10 Manual.Count131072.C069190.packed 64 cuts69190 = true := by
 decide +kernel
def cuts69191 : List PrefixCut := [⟨63,173916942,173917044⟩,
⟨64,176678001,176678104⟩]
theorem checked69191 : checkPrefixCuts (2^48) 9072934913 10 Manual.Count131072.C069191.packed 64 cuts69191 = true := by
 decide +kernel
def pointBounds69191 : List (Nat × Nat × Nat) := [(9073063936,115671320177722,115671709599188)]
theorem point_links_checked69191 : (cuts69191.take 1).map (fun c => (9072934913-1+2*2^10*c.k,115671146260780+c.lower,115671535682144+c.upper)) = pointBounds69191 := by
 decide +kernel
def cuts69192 : List PrefixCut := [⟨64,179653638,179653743⟩]
theorem checked69192 : checkPrefixCuts (2^48) 9073065985 10 Manual.Count131072.C069192.packed 64 cuts69192 = true := by
 decide +kernel
def cuts69193 : List PrefixCut := [⟨64,178906519,178906617⟩]
theorem checked69193 : checkPrefixCuts (2^48) 9073197057 10 Manual.Count131072.C069193.packed 64 cuts69193 = true := by
 decide +kernel
def cuts69194 : List PrefixCut := [⟨10,28416332,28416350⟩,
⟨64,175956840,175956945⟩]
theorem checked69194 : checkPrefixCuts (2^48) 9073328129 10 Manual.Count131072.C069194.packed 64 cuts69194 = true := by
 decide +kernel
def pointBounds69194 : List (Nat × Nat × Nat) := [(9073348608,115671709915270,115672099336958)]
theorem point_links_checked69194 : (cuts69194.take 1).map (fun c => (9073328129-1+2*2^10*c.k,115671681498938+c.lower,115672070920608+c.upper)) = pointBounds69194 := by
 decide +kernel
def cuts69195 : List PrefixCut := [⟨64,177412300,177412405⟩]
theorem checked69195 : checkPrefixCuts (2^48) 9073459201 10 Manual.Count131072.C069195.packed 64 cuts69195 = true := by
 decide +kernel
def cuts69196 : List PrefixCut := [⟨21,58940400,58940433⟩,
⟨64,176789328,176789435⟩]
theorem checked69196 : checkPrefixCuts (2^48) 9073590273 10 Manual.Count131072.C069196.packed 64 cuts69196 = true := by
 decide +kernel
def pointBounds69196 : List (Nat × Nat × Nat) := [(9073633280,115672093808478,115672483230391)]
theorem point_links_checked69196 : (cuts69196.take 1).map (fun c => (9073590273-1+2*2^10*c.k,115672034868078+c.lower,115672424289958+c.upper)) = pointBounds69196 := by
 decide +kernel
def cuts69197 : List PrefixCut := [⟨64,177717389,177717491⟩]
theorem checked69197 : checkPrefixCuts (2^48) 9073721345 10 Manual.Count131072.C069197.packed 64 cuts69197 = true := by
 decide +kernel
def cuts69198 : List PrefixCut := [⟨32,88438957,88439009⟩,
⟨64,177032377,177032478⟩]
theorem checked69198 : checkPrefixCuts (2^48) 9073852417 10 Manual.Count131072.C069198.packed 64 cuts69198 = true := by
 decide +kernel
def pointBounds69198 : List (Nat × Nat × Nat) := [(9073917952,115672477813752,115672867235893)]
theorem point_links_checked69198 : (cuts69198.take 1).map (fun c => (9073852417-1+2*2^10*c.k,115672389374795+c.lower,115672778796884+c.upper)) = pointBounds69198 := by
 decide +kernel
def cuts69199 : List PrefixCut := [⟨64,177464084,177464181⟩]
theorem checked69199 : checkPrefixCuts (2^48) 9073983489 10 Manual.Count131072.C069199.packed 64 cuts69199 = true := by
 decide +kernel
def cuts69200 : List PrefixCut := [⟨43,118835297,118835366⟩,
⟨64,177182354,177182456⟩]
theorem checked69200 : checkPrefixCuts (2^48) 9074114561 10 Manual.Count131072.C069200.packed 64 cuts69200 = true := by
 decide +kernel
def pointBounds69200 : List (Nat × Nat × Nat) := [(9074202624,115672862706553,115673252128909)]
theorem point_links_checked69200 : (cuts69200.take 1).map (fun c => (9074114561-1+2*2^10*c.k,115672743871256+c.lower,115673133293543+c.upper)) = pointBounds69200 := by
 decide +kernel
def cuts69201 : List PrefixCut := [⟨64,173736698,173736799⟩]
theorem checked69201 : checkPrefixCuts (2^48) 9074245633 10 Manual.Count131072.C069201.packed 64 cuts69201 = true := by
 decide +kernel
def cuts69202 : List PrefixCut := [⟨54,152393694,152393781⟩,
⟨64,179937887,179937988⟩]
theorem checked69202 : checkPrefixCuts (2^48) 9074376705 10 Manual.Count131072.C069202.packed 64 cuts69202 = true := by
 decide +kernel
def pointBounds69202 : List (Nat × Nat × Nat) := [(9074487296,115673247184002,115673636606579)]
theorem point_links_checked69202 : (cuts69202.take 1).map (fun c => (9074376705-1+2*2^10*c.k,115673094790308+c.lower,115673484212798+c.upper)) = pointBounds69202 := by
 decide +kernel
def cuts69203 : List PrefixCut := [⟨64,178136226,178136332⟩]
theorem checked69203 : checkPrefixCuts (2^48) 9074507777 10 Manual.Count131072.C069203.packed 64 cuts69203 = true := by
 decide +kernel
def cuts69204 : List PrefixCut := [⟨64,176272599,176272705⟩]
theorem checked69204 : checkPrefixCuts (2^48) 9074638849 10 Manual.Count131072.C069204.packed 64 cuts69204 = true := by
 decide +kernel
def cuts69205 : List PrefixCut := [⟨1,2140194,2140195⟩,
⟨64,177200576,177200681⟩]
theorem checked69205 : checkPrefixCuts (2^48) 9074769921 10 Manual.Count131072.C069205.packed 64 cuts69205 = true := by
 decide +kernel
def pointBounds69205 : List (Nat × Nat × Nat) := [(9074771968,115673631277214,115674020700018)]
theorem point_links_checked69205 : (cuts69205.take 1).map (fun c => (9074769921-1+2*2^10*c.k,115673629137020+c.lower,115674018559823+c.upper)) = pointBounds69205 := by
 decide +kernel
def cuts69206 : List PrefixCut := [⟨64,179400210,179400311⟩]
theorem checked69206 : checkPrefixCuts (2^48) 9074900993 10 Manual.Count131072.C069206.packed 64 cuts69206 = true := by
 decide +kernel
def cuts69207 : List PrefixCut := [⟨12,33528690,33528710⟩,
⟨64,175086356,175086459⟩]
theorem checked69207 : checkPrefixCuts (2^48) 9075032065 10 Manual.Count131072.C069207.packed 64 cuts69207 = true := by
 decide +kernel
def pointBounds69207 : List (Nat × Nat × Nat) := [(9075056640,115674019266496,115674408689525)]
theorem point_links_checked69207 : (cuts69207.take 1).map (fun c => (9075032065-1+2*2^10*c.k,115673985737806+c.lower,115674375160815+c.upper)) = pointBounds69207 := by
 decide +kernel
def cuts69208 : List PrefixCut := [⟨64,178867742,178867851⟩]
theorem checked69208 : checkPrefixCuts (2^48) 9075163137 10 Manual.Count131072.C069208.packed 64 cuts69208 = true := by
 decide +kernel
def cuts69209 : List PrefixCut := [⟨23,62278983,62279020⟩,
⟨64,175453476,175453576⟩]
theorem checked69209 : checkPrefixCuts (2^48) 9075294209 10 Manual.Count131072.C069209.packed 64 cuts69209 = true := by
 decide +kernel
def pointBounds69209 : List (Nat × Nat × Nat) := [(9075341312,115674401970887,115674791394145)]
theorem point_links_checked69209 : (cuts69209.take 1).map (fun c => (9075294209-1+2*2^10*c.k,115674339691904+c.lower,115674729115125+c.upper)) = pointBounds69209 := by
 decide +kernel
def cuts69210 : List PrefixCut := [⟨64,176474445,176474551⟩]
theorem checked69210 : checkPrefixCuts (2^48) 9075425281 10 Manual.Count131072.C069210.packed 64 cuts69210 = true := by
 decide +kernel
def cuts69211 : List PrefixCut := [⟨34,94253056,94253110⟩,
⟨64,174797122,174797218⟩]
theorem checked69211 : checkPrefixCuts (2^48) 9075556353 10 Manual.Count131072.C069211.packed 64 cuts69211 = true := by
 decide +kernel
def pointBounds69211 : List (Nat × Nat × Nat) := [(9075625984,115674785872881,115675175296362)]
theorem point_links_checked69211 : (cuts69211.take 1).map (fun c => (9075556353-1+2*2^10*c.k,115674691619825+c.lower,115675081043252+c.upper)) = pointBounds69211 := by
 decide +kernel
def cuts69212 : List PrefixCut := [⟨64,180128970,180129078⟩]
theorem checked69212 : checkPrefixCuts (2^48) 9075687425 10 Manual.Count131072.C069212.packed 64 cuts69212 = true := by
 decide +kernel
def cuts69213 : List PrefixCut := [⟨45,124643504,124643579⟩,
⟨64,177986445,177986550⟩]
theorem checked69213 : checkPrefixCuts (2^48) 9075818497 10 Manual.Count131072.C069213.packed 64 cuts69213 = true := by
 decide +kernel
def pointBounds69213 : List (Nat × Nat × Nat) := [(9075910656,115675171189421,115675560613127)]
theorem point_links_checked69213 : (cuts69213.take 1).map (fun c => (9075818497-1+2*2^10*c.k,115675046545917+c.lower,115675435969548+c.upper)) = pointBounds69213 := by
 decide +kernel
def cuts69214 : List PrefixCut := [⟨64,178883259,178883363⟩]
theorem checked69214 : checkPrefixCuts (2^48) 9075949569 10 Manual.Count131072.C069214.packed 64 cuts69214 = true := by
 decide +kernel
def cuts69215 : List PrefixCut := [⟨56,155621372,155621462⟩,
⟨64,177019931,177020033⟩]
theorem checked69215 : checkPrefixCuts (2^48) 9076080641 10 Manual.Count131072.C069215.packed 64 cuts69215 = true := by
 decide +kernel
def pointBounds69215 : List (Nat × Nat × Nat) := [(9076195328,115675559036993,115675948460923)]
theorem point_links_checked69215 : (cuts69215.take 1).map (fun c => (9076080641-1+2*2^10*c.k,115675403415621+c.lower,115675792839461+c.upper)) = pointBounds69215 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000287
