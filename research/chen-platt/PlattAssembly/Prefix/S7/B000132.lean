import PlattAssemblyKernel
import PlattCertificates.Count131072.C064224
import PlattCertificates.Count131072.C064225
import PlattCertificates.Count131072.C064226
import PlattCertificates.Count131072.C064227
import PlattCertificates.Count131072.C064228
import PlattCertificates.Count131072.C064229
import PlattCertificates.Count131072.C064230
import PlattCertificates.Count131072.C064231
import PlattCertificates.Count131072.C064232
import PlattCertificates.Count131072.C064233
import PlattCertificates.Count131072.C064234
import PlattCertificates.Count131072.C064235
import PlattCertificates.Count131072.C064236
import PlattCertificates.Count131072.C064237
import PlattCertificates.Count131072.C064238
import PlattCertificates.Count131072.C064239
import PlattCertificates.Count131072.C064240
import PlattCertificates.Count131072.C064241
import PlattCertificates.Count131072.C064242
import PlattCertificates.Count131072.C064243
import PlattCertificates.Count131072.C064244
import PlattCertificates.Count131072.C064245
import PlattCertificates.Count131072.C064246
import PlattCertificates.Count131072.C064247
import PlattCertificates.Count131072.C064248
import PlattCertificates.Count131072.C064249
import PlattCertificates.Count131072.C064250
import PlattCertificates.Count131072.C064251
import PlattCertificates.Count131072.C064252
import PlattCertificates.Count131072.C064253
import PlattCertificates.Count131072.C064254
import PlattCertificates.Count131072.C064255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000132
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64224 : List PrefixCut := [⟨46,137663547,137663623⟩,
⟨64,192909014,192909120⟩]
theorem checked64224 : checkPrefixCuts (2^48) 8421900289 10 Manual.Count131072.C064224.packed 64 cuts64224 = true := by
 decide +kernel
def pointBounds64224 : List (Nat × Nat × Nat) := [(8421994496,114755739694881,114756128583586)]
theorem point_links_checked64224 : (cuts64224.take 1).map (fun c => (8421900289-1+2*2^10*c.k,114755602031334+c.lower,114755990919963+c.upper)) = pointBounds64224 := by
 decide +kernel
def cuts64225 : List PrefixCut := [⟨64,191636018,191636130⟩]
theorem checked64225 : checkPrefixCuts (2^48) 8422031361 10 Manual.Count131072.C064225.packed 64 cuts64225 = true := by
 decide +kernel
def cuts64226 : List PrefixCut := [⟨47,143641510,143641588⟩,
⟨64,195910843,195910949⟩]
theorem checked64226 : checkPrefixCuts (2^48) 8422162433 10 Manual.Count131072.C064226.packed 64 cuts64226 = true := by
 decide +kernel
def pointBounds64226 : List (Nat × Nat × Nat) := [(8422258688,114756130217876,114756519106801)]
theorem point_links_checked64226 : (cuts64226.take 1).map (fun c => (8422162433-1+2*2^10*c.k,114755986576366+c.lower,114756375465213+c.upper)) = pointBounds64226 := by
 decide +kernel
def cuts64227 : List PrefixCut := [⟨64,191095334,191095439⟩]
theorem checked64227 : checkPrefixCuts (2^48) 8422293505 10 Manual.Count131072.C064227.packed 64 cuts64227 = true := by
 decide +kernel
def cuts64228 : List PrefixCut := [⟨48,143870964,143871044⟩,
⟨64,191593646,191593753⟩]
theorem checked64228 : checkPrefixCuts (2^48) 8422424577 10 Manual.Count131072.C064228.packed 64 cuts64228 = true := by
 decide +kernel
def pointBounds64228 : List (Nat × Nat × Nat) := [(8422522880,114756517453507,114756906342645)]
theorem point_links_checked64228 : (cuts64228.take 1).map (fun c => (8422424577-1+2*2^10*c.k,114756373582543+c.lower,114756762471601+c.upper)) = pointBounds64228 := by
 decide +kernel
def cuts64229 : List PrefixCut := [⟨64,192225617,192225729⟩]
theorem checked64229 : checkPrefixCuts (2^48) 8422555649 10 Manual.Count131072.C064229.packed 64 cuts64229 = true := by
 decide +kernel
def cuts64230 : List PrefixCut := [⟨49,149079742,149079828⟩,
⟨64,193024675,193024785⟩]
theorem checked64230 : checkPrefixCuts (2^48) 8422686721 10 Manual.Count131072.C064230.packed 64 cuts64230 = true := by
 decide +kernel
def pointBounds64230 : List (Nat × Nat × Nat) := [(8422787072,114756906481548,114757295370911)]
theorem point_links_checked64230 : (cuts64230.take 1).map (fun c => (8422686721-1+2*2^10*c.k,114756757401806+c.lower,114757146291083+c.upper)) = pointBounds64230 := by
 decide +kernel
def cuts64231 : List PrefixCut := [⟨64,190481908,190482019⟩]
theorem checked64231 : checkPrefixCuts (2^48) 8422817793 10 Manual.Count131072.C064231.packed 64 cuts64231 = true := by
 decide +kernel
def cuts64232 : List PrefixCut := [⟨50,149075093,149075179⟩,
⟨64,191615130,191615241⟩]
theorem checked64232 : checkPrefixCuts (2^48) 8422948865 10 Manual.Count131072.C064232.packed 64 cuts64232 = true := by
 decide +kernel
def pointBounds64232 : List (Nat × Nat × Nat) := [(8423051264,114757289983482,114757678873066)]
theorem point_links_checked64232 : (cuts64232.take 1).map (fun c => (8422948865-1+2*2^10*c.k,114757140908389+c.lower,114757529797887+c.upper)) = pointBounds64232 := by
 decide +kernel
def cuts64233 : List PrefixCut := [⟨64,193583746,193583855⟩]
theorem checked64233 : checkPrefixCuts (2^48) 8423079937 10 Manual.Count131072.C064233.packed 64 cuts64233 = true := by
 decide +kernel
def cuts64234 : List PrefixCut := [⟨51,151977656,151977739⟩,
⟨64,191308421,191308526⟩]
theorem checked64234 : checkPrefixCuts (2^48) 8423211009 10 Manual.Count131072.C064234.packed 64 cuts64234 = true := by
 decide +kernel
def pointBounds64234 : List (Nat × Nat × Nat) := [(8423315456,114757678084921,114758066974722)]
theorem point_links_checked64234 : (cuts64234.take 1).map (fun c => (8423211009-1+2*2^10*c.k,114757526107265+c.lower,114757914996983+c.upper)) = pointBounds64234 := by
 decide +kernel
def cuts64235 : List PrefixCut := [⟨64,189434175,189434287⟩]
theorem checked64235 : checkPrefixCuts (2^48) 8423342081 10 Manual.Count131072.C064235.packed 64 cuts64235 = true := by
 decide +kernel
def cuts64236 : List PrefixCut := [⟨52,155113952,155114036⟩,
⟨64,192037602,192037705⟩]
theorem checked64236 : checkPrefixCuts (2^48) 8423473153 10 Manual.Count131072.C064236.packed 64 cuts64236 = true := by
 decide +kernel
def pointBounds64236 : List (Nat × Nat × Nat) := [(8423579648,114758061963813,114758450853832)]
theorem point_links_checked64236 : (cuts64236.take 1).map (fun c => (8423473153-1+2*2^10*c.k,114757906849861+c.lower,114758295739796+c.upper)) = pointBounds64236 := by
 decide +kernel
def cuts64237 : List PrefixCut := [⟨64,190397298,190397405⟩]
theorem checked64237 : checkPrefixCuts (2^48) 8423604225 10 Manual.Count131072.C064237.packed 64 cuts64237 = true := by
 decide +kernel
def cuts64238 : List PrefixCut := [⟨53,162460249,162460341⟩,
⟨64,195907687,195907798⟩]
theorem checked64238 : checkPrefixCuts (2^48) 8423735297 10 Manual.Count131072.C064238.packed 64 cuts64238 = true := by
 decide +kernel
def pointBounds64238 : List (Nat × Nat × Nat) := [(8423843840,114758451745010,114758840635247)]
theorem point_links_checked64238 : (cuts64238.take 1).map (fun c => (8423735297-1+2*2^10*c.k,114758289284761+c.lower,114758678174906+c.upper)) = pointBounds64238 := by
 decide +kernel
def cuts64239 : List PrefixCut := [⟨64,193264935,193265048⟩]
theorem checked64239 : checkPrefixCuts (2^48) 8423866369 10 Manual.Count131072.C064239.packed 64 cuts64239 = true := by
 decide +kernel
def cuts64240 : List PrefixCut := [⟨54,159848943,159849037⟩,
⟨64,190254755,190254867⟩]
theorem checked64240 : checkPrefixCuts (2^48) 8423997441 10 Manual.Count131072.C064240.packed 64 cuts64240 = true := by
 decide +kernel
def pointBounds64240 : List (Nat × Nat × Nat) := [(8424108032,114758838306326,114759227196789)]
theorem point_links_checked64240 : (cuts64240.take 1).map (fun c => (8423997441-1+2*2^10*c.k,114758678457383+c.lower,114759067347752+c.upper)) = pointBounds64240 := by
 decide +kernel
def cuts64241 : List PrefixCut := [⟨64,193225521,193225631⟩]
theorem checked64241 : checkPrefixCuts (2^48) 8424128513 10 Manual.Count131072.C064241.packed 64 cuts64241 = true := by
 decide +kernel
def cuts64242 : List PrefixCut := [⟨55,168364045,168364142⟩,
⟨64,194759475,194759586⟩]
theorem checked64242 : checkPrefixCuts (2^48) 8424259585 10 Manual.Count131072.C064242.packed 64 cuts64242 = true := by
 decide +kernel
def pointBounds64242 : List (Nat × Nat × Nat) := [(8424372224,114759230301704,114759619192392)]
theorem point_links_checked64242 : (cuts64242.take 1).map (fun c => (8424259585-1+2*2^10*c.k,114759061937659+c.lower,114759450828250+c.upper)) = pointBounds64242 := by
 decide +kernel
def cuts64243 : List PrefixCut := [⟨64,193286342,193286455⟩]
theorem checked64243 : checkPrefixCuts (2^48) 8424390657 10 Manual.Count131072.C064243.packed 64 cuts64243 = true := by
 decide +kernel
def cuts64244 : List PrefixCut := [⟨56,168525835,168525939⟩,
⟨64,192681912,192682029⟩]
theorem checked64244 : checkPrefixCuts (2^48) 8424521729 10 Manual.Count131072.C064244.packed 64 cuts64244 = true := by
 decide +kernel
def pointBounds64244 : List (Nat × Nat × Nat) := [(8424636416,114759618509311,114760007400230)]
theorem point_links_checked64244 : (cuts64244.take 1).map (fun c => (8424521729-1+2*2^10*c.k,114759449983476+c.lower,114759838874291+c.upper)) = pointBounds64244 := by
 decide +kernel
def cuts64245 : List PrefixCut := [⟨64,190707703,190707813⟩]
theorem checked64245 : checkPrefixCuts (2^48) 8424652801 10 Manual.Count131072.C064245.packed 64 cuts64245 = true := by
 decide +kernel
def cuts64246 : List PrefixCut := [⟨57,167952625,167952720⟩,
⟨64,189468567,189468674⟩]
theorem checked64246 : checkPrefixCuts (2^48) 8424783873 10 Manual.Count131072.C064246.packed 64 cuts64246 = true := by
 decide +kernel
def pointBounds64246 : List (Nat × Nat × Nat) := [(8424900608,114760001325716,114760390216853)]
theorem point_links_checked64246 : (cuts64246.take 1).map (fun c => (8424783873-1+2*2^10*c.k,114759833373091+c.lower,114760222264133+c.upper)) = pointBounds64246 := by
 decide +kernel
def cuts64247 : List PrefixCut := [⟨64,192906806,192906921⟩]
theorem checked64247 : checkPrefixCuts (2^48) 8424914945 10 Manual.Count131072.C064247.packed 64 cuts64247 = true := by
 decide +kernel
def cuts64248 : List PrefixCut := [⟨58,174495547,174495643⟩,
⟨64,192135397,192135502⟩]
theorem checked64248 : checkPrefixCuts (2^48) 8425046017 10 Manual.Count131072.C064248.packed 64 cuts64248 = true := by
 decide +kernel
def pointBounds64248 : List (Nat × Nat × Nat) := [(8425164800,114760390244011,114760779135371)]
theorem point_links_checked64248 : (cuts64248.take 1).map (fun c => (8425046017-1+2*2^10*c.k,114760215748464+c.lower,114760604639728+c.upper)) = pointBounds64248 := by
 decide +kernel
def cuts64249 : List PrefixCut := [⟨64,191196962,191197069⟩]
theorem checked64249 : checkPrefixCuts (2^48) 8425177089 10 Manual.Count131072.C064249.packed 64 cuts64249 = true := by
 decide +kernel
def cuts64250 : List PrefixCut := [⟨59,178131570,178131670⟩,
⟨64,192897801,192897909⟩]
theorem checked64250 : checkPrefixCuts (2^48) 8425308161 10 Manual.Count131072.C064250.packed 64 cuts64250 = true := by
 decide +kernel
def pointBounds64250 : List (Nat × Nat × Nat) := [(8425428992,114760777212393,114761166103969)]
theorem point_links_checked64250 : (cuts64250.take 1).map (fun c => (8425308161-1+2*2^10*c.k,114760599080823+c.lower,114760987972299+c.upper)) = pointBounds64250 := by
 decide +kernel
def cuts64251 : List PrefixCut := [⟨64,193362491,193362597⟩]
theorem checked64251 : checkPrefixCuts (2^48) 8425439233 10 Manual.Count131072.C064251.packed 64 cuts64251 = true := by
 decide +kernel
def cuts64252 : List PrefixCut := [⟨60,177457872,177457977⟩,
⟨64,189217037,189217149⟩]
theorem checked64252 : checkPrefixCuts (2^48) 8425570305 10 Manual.Count131072.C064252.packed 64 cuts64252 = true := by
 decide +kernel
def pointBounds64252 : List (Nat × Nat × Nat) := [(8425693184,114761162798987,114761551690782)]
theorem point_links_checked64252 : (cuts64252.take 1).map (fun c => (8425570305-1+2*2^10*c.k,114760985341115+c.lower,114761374232805+c.upper)) = pointBounds64252 := by
 decide +kernel
def cuts64253 : List PrefixCut := [⟨64,188278706,188278814⟩]
theorem checked64253 : checkPrefixCuts (2^48) 8425701377 10 Manual.Count131072.C064253.packed 64 cuts64253 = true := by
 decide +kernel
def cuts64254 : List PrefixCut := [⟨61,179890965,179891072⟩,
⟨64,188275790,188275901⟩]
theorem checked64254 : checkPrefixCuts (2^48) 8425832449 10 Manual.Count131072.C064254.packed 64 cuts64254 = true := by
 decide +kernel
def pointBounds64254 : List (Nat × Nat × Nat) := [(8425957376,114761542727823,114761931619840)]
theorem point_links_checked64254 : (cuts64254.take 1).map (fun c => (8425832449-1+2*2^10*c.k,114761362836858+c.lower,114761751728768+c.upper)) = pointBounds64254 := by
 decide +kernel
def cuts64255 : List PrefixCut := [⟨64,189141400,189141516⟩]
theorem checked64255 : checkPrefixCuts (2^48) 8425963521 10 Manual.Count131072.C064255.packed 64 cuts64255 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000132
