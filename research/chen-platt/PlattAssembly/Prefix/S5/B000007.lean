import PlattAssemblyKernel
import PlattCertificates.Count131072.C040224
import PlattCertificates.Count131072.C040225
import PlattCertificates.Count131072.C040226
import PlattCertificates.Count131072.C040227
import PlattCertificates.Count131072.C040228
import PlattCertificates.Count131072.C040229
import PlattCertificates.Count131072.C040230
import PlattCertificates.Count131072.C040231
import PlattCertificates.Count131072.C040232
import PlattCertificates.Count131072.C040233
import PlattCertificates.Count131072.C040234
import PlattCertificates.Count131072.C040235
import PlattCertificates.Count131072.C040236
import PlattCertificates.Count131072.C040237
import PlattCertificates.Count131072.C040238
import PlattCertificates.Count131072.C040239
import PlattCertificates.Count131072.C040240
import PlattCertificates.Count131072.C040241
import PlattCertificates.Count131072.C040242
import PlattCertificates.Count131072.C040243
import PlattCertificates.Count131072.C040244
import PlattCertificates.Count131072.C040245
import PlattCertificates.Count131072.C040246
import PlattCertificates.Count131072.C040247
import PlattCertificates.Count131072.C040248
import PlattCertificates.Count131072.C040249
import PlattCertificates.Count131072.C040250
import PlattCertificates.Count131072.C040251
import PlattCertificates.Count131072.C040252
import PlattCertificates.Count131072.C040253
import PlattCertificates.Count131072.C040254
import PlattCertificates.Count131072.C040255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40224 : List PrefixCut := [⟨28,135984123,135984202⟩,
⟨64,309416411,309416592⟩]
theorem checked40224 : checkPrefixCuts (2^48) 5276172289 10 Manual.Count131072.C040224.packed 64 cuts40224 = true := by
 decide +kernel
def pointBounds40224 : List (Nat × Nat × Nat) := [(5276229632,108936535176816,108936920724190)]
theorem point_links_checked40224 : (cuts40224.take 1).map (fun c => (5276172289-1+2*2^10*c.k,108936399192693+c.lower,108936784739988+c.upper)) = pointBounds40224 := by
 decide +kernel
def cuts40225 : List PrefixCut := [⟨45,221388083,221388213⟩,
⟨64,316450407,316450593⟩]
theorem checked40225 : checkPrefixCuts (2^48) 5276303361 10 Manual.Count131072.C040225.packed 64 cuts40225 = true := by
 decide +kernel
def pointBounds40225 : List (Nat × Nat × Nat) := [(5276395520,108936929997187,108937315544793)]
theorem point_links_checked40225 : (cuts40225.take 1).map (fun c => (5276303361-1+2*2^10*c.k,108936708609104+c.lower,108937094156580+c.upper)) = pointBounds40225 := by
 decide +kernel
def cuts40226 : List PrefixCut := [⟨62,303693231,303693408⟩,
⟨64,313615282,313615465⟩]
theorem checked40226 : checkPrefixCuts (2^48) 5276434433 10 Manual.Count131072.C040226.packed 64 cuts40226 = true := by
 decide +kernel
def pointBounds40226 : List (Nat × Nat × Nat) := [(5276561408,108937328752742,108937714300581)]
theorem point_links_checked40226 : (cuts40226.take 1).map (fun c => (5276434433-1+2*2^10*c.k,108937025059511+c.lower,108937410607173+c.upper)) = pointBounds40226 := by
 decide +kernel
def cuts40227 : List PrefixCut := [⟨64,314727693,314727884⟩]
theorem checked40227 : checkPrefixCuts (2^48) 5276565505 10 Manual.Count131072.C040227.packed 64 cuts40227 = true := by
 decide +kernel
def cuts40228 : List PrefixCut := [⟨15,73453116,73453160⟩,
⟨64,313492992,313493178⟩]
theorem checked40228 : checkPrefixCuts (2^48) 5276696577 10 Manual.Count131072.C040228.packed 64 cuts40228 = true := by
 decide +kernel
def pointBounds40228 : List (Nat × Nat × Nat) := [(5276727296,108937726855602,108938112403682)]
theorem point_links_checked40228 : (cuts40228.take 1).map (fun c => (5276696577-1+2*2^10*c.k,108937653402486+c.lower,108938038950522+c.upper)) = pointBounds40228 := by
 decide +kernel
def cuts40229 : List PrefixCut := [⟨32,155543407,155543499⟩,
⟨64,307724409,307724590⟩]
theorem checked40229 : checkPrefixCuts (2^48) 5276827649 10 Manual.Count131072.C040229.packed 64 cuts40229 = true := by
 decide +kernel
def pointBounds40229 : List (Nat × Nat × Nat) := [(5276893184,108938122438885,108938507987199)]
theorem point_links_checked40229 : (cuts40229.take 1).map (fun c => (5276827649-1+2*2^10*c.k,108937966895478+c.lower,108938352443700+c.upper)) = pointBounds40229 := by
 decide +kernel
def cuts40230 : List PrefixCut := [⟨49,240776087,240776232⟩,
⟨64,316997793,316997984⟩]
theorem checked40230 : checkPrefixCuts (2^48) 5276958721 10 Manual.Count131072.C040230.packed 64 cuts40230 = true := by
 decide +kernel
def pointBounds40230 : List (Nat × Nat × Nat) := [(5277059072,108938515395974,108938900944522)]
theorem point_links_checked40230 : (cuts40230.take 1).map (fun c => (5276958721-1+2*2^10*c.k,108938274619887+c.lower,108938660168290+c.upper)) = pointBounds40230 := by
 decide +kernel
def cuts40231 : List PrefixCut := [⟨64,307069035,307069217⟩]
theorem checked40231 : checkPrefixCuts (2^48) 5277089793 10 Manual.Count131072.C040231.packed 64 cuts40231 = true := by
 decide +kernel
def cuts40232 : List PrefixCut := [⟨2,9974148,9974154⟩,
⟨64,314208583,314208766⟩]
theorem checked40232 : checkPrefixCuts (2^48) 5277220865 10 Manual.Count131072.C040232.packed 64 cuts40232 = true := by
 decide +kernel
def pointBounds40232 : List (Nat × Nat × Nat) := [(5277224960,108938908660863,108939294209645)]
theorem point_links_checked40232 : (cuts40232.take 1).map (fun c => (5277220865-1+2*2^10*c.k,108938898686715+c.lower,108939284235491+c.upper)) = pointBounds40232 := by
 decide +kernel
def cuts40233 : List PrefixCut := [⟨19,90404846,90404902⟩,
⟨64,309187215,309187402⟩]
theorem checked40233 : checkPrefixCuts (2^48) 5277351937 10 Manual.Count131072.C040233.packed 64 cuts40233 = true := by
 decide +kernel
def pointBounds40233 : List (Nat × Nat × Nat) := [(5277390848,108939303300144,108939688849159)]
theorem point_links_checked40233 : (cuts40233.take 1).map (fun c => (5277351937-1+2*2^10*c.k,108939212895298+c.lower,108939598444257+c.upper)) = pointBounds40233 := by
 decide +kernel
def cuts40234 : List PrefixCut := [⟨36,176644496,176644602⟩,
⟨64,315632971,315633159⟩]
theorem checked40234 : checkPrefixCuts (2^48) 5277483009 10 Manual.Count131072.C040234.packed 64 cuts40234 = true := by
 decide +kernel
def pointBounds40234 : List (Nat × Nat × Nat) := [(5277556736,108939698727009,108940084276261)]
theorem point_links_checked40234 : (cuts40234.take 1).map (fun c => (5277483009-1+2*2^10*c.k,108939522082513+c.lower,108939907631659+c.upper)) = pointBounds40234 := by
 decide +kernel
def cuts40235 : List PrefixCut := [⟨53,257119326,257119485⟩,
⟨64,311785170,311785362⟩]
theorem checked40235 : checkPrefixCuts (2^48) 5277614081 10 Manual.Count131072.C040235.packed 64 cuts40235 = true := by
 decide +kernel
def pointBounds40235 : List (Nat × Nat × Nat) := [(5277722624,108940094834810,108940480384303)]
theorem point_links_checked40235 : (cuts40235.take 1).map (fun c => (5277614081-1+2*2^10*c.k,108939837715484+c.lower,108940223264818+c.upper)) = pointBounds40235 := by
 decide +kernel
def cuts40236 : List PrefixCut := [⟨64,311777406,311777592⟩]
theorem checked40236 : checkPrefixCuts (2^48) 5277745153 10 Manual.Count131072.C040236.packed 64 cuts40236 = true := by
 decide +kernel
def cuts40237 : List PrefixCut := [⟨6,30825336,30825354⟩,
⟨64,315929472,315929658⟩]
theorem checked40237 : checkPrefixCuts (2^48) 5277876225 10 Manual.Count131072.C040237.packed 64 cuts40237 = true := by
 decide +kernel
def pointBounds40237 : List (Nat × Nat × Nat) := [(5277888512,108940492103396,108940877653126)]
theorem point_links_checked40237 : (cuts40237.take 1).map (fun c => (5277876225-1+2*2^10*c.k,108940461278060+c.lower,108940846827772+c.upper)) = pointBounds40237 := by
 decide +kernel
def cuts40238 : List PrefixCut := [⟨23,111032084,111032149⟩,
⟨64,312721850,312722033⟩]
theorem checked40238 : checkPrefixCuts (2^48) 5278007297 10 Manual.Count131072.C040238.packed 64 cuts40238 = true := by
 decide +kernel
def pointBounds40238 : List (Nat × Nat × Nat) := [(5278054400,108940888239616,108941273789579)]
theorem point_links_checked40238 : (cuts40238.take 1).map (fun c => (5278007297-1+2*2^10*c.k,108940777207532+c.lower,108941162757430+c.upper)) = pointBounds40238 := by
 decide +kernel
def cuts40239 : List PrefixCut := [⟨40,198486912,198487030⟩,
⟨64,312927443,312927629⟩]
theorem checked40239 : checkPrefixCuts (2^48) 5278138369 10 Manual.Count131072.C040239.packed 64 cuts40239 = true := by
 decide +kernel
def pointBounds40239 : List (Nat × Nat × Nat) := [(5278220288,108941288416294,108941673966493)]
theorem point_links_checked40239 : (cuts40239.take 1).map (fun c => (5278138369-1+2*2^10*c.k,108941089929382+c.lower,108941475479463+c.upper)) = pointBounds40239 := by
 decide +kernel
def cuts40240 : List PrefixCut := [⟨57,278684435,278684607⟩,
⟨64,311586491,311586683⟩]
theorem checked40240 : checkPrefixCuts (2^48) 5278269441 10 Manual.Count131072.C040240.packed 64 cuts40240 = true := by
 decide +kernel
def pointBounds40240 : List (Nat × Nat × Nat) := [(5278386176,108941681541260,108942067091699)]
theorem point_links_checked40240 : (cuts40240.take 1).map (fun c => (5278269441-1+2*2^10*c.k,108941402856825+c.lower,108941788407092+c.upper)) = pointBounds40240 := by
 decide +kernel
def cuts40241 : List PrefixCut := [⟨64,315524787,315524978⟩]
theorem checked40241 : checkPrefixCuts (2^48) 5278400513 10 Manual.Count131072.C040241.packed 64 cuts40241 = true := by
 decide +kernel
def cuts40242 : List PrefixCut := [⟨10,48845119,48845149⟩,
⟨64,312050928,312051114⟩]
theorem checked40242 : checkPrefixCuts (2^48) 5278531585 10 Manual.Count131072.C040242.packed 64 cuts40242 = true := by
 decide +kernel
def pointBounds40242 : List (Nat × Nat × Nat) := [(5278552064,108942078813222,108942464363902)]
theorem point_links_checked40242 : (cuts40242.take 1).map (fun c => (5278531585-1+2*2^10*c.k,108942029968103+c.lower,108942415518753+c.upper)) = pointBounds40242 := by
 decide +kernel
def cuts40243 : List PrefixCut := [⟨27,128614748,128614827⟩,
⟨64,308097287,308097474⟩]
theorem checked40243 : checkPrefixCuts (2^48) 5278662657 10 Manual.Count131072.C040243.packed 64 cuts40243 = true := by
 decide +kernel
def pointBounds40243 : List (Nat × Nat × Nat) := [(5278717952,108942470633779,108942856184694)]
theorem point_links_checked40243 : (cuts40243.take 1).map (fun c => (5278662657-1+2*2^10*c.k,108942342019031+c.lower,108942727569867+c.upper)) = pointBounds40243 := by
 decide +kernel
def cuts40244 : List PrefixCut := [⟨44,211845790,211845916⟩,
⟨64,308462907,308463090⟩]
theorem checked40244 : checkPrefixCuts (2^48) 5278793729 10 Manual.Count131072.C040244.packed 64 cuts40244 = true := by
 decide +kernel
def pointBounds40244 : List (Nat × Nat × Nat) := [(5278883840,108942861962108,108943247513257)]
theorem point_links_checked40244 : (cuts40244.take 1).map (fun c => (5278793729-1+2*2^10*c.k,108942650116318+c.lower,108943035667341+c.upper)) = pointBounds40244 := by
 decide +kernel
def cuts40245 : List PrefixCut := [⟨61,296991645,296991817⟩,
⟨64,312614172,312614352⟩]
theorem checked40245 : checkPrefixCuts (2^48) 5278924801 10 Manual.Count131072.C040245.packed 64 cuts40245 = true := by
 decide +kernel
def pointBounds40245 : List (Nat × Nat × Nat) := [(5279049728,108943255570870,108943641122248)]
theorem point_links_checked40245 : (cuts40245.take 1).map (fun c => (5278924801-1+2*2^10*c.k,108942958579225+c.lower,108943344130431+c.upper)) = pointBounds40245 := by
 decide +kernel
def cuts40246 : List PrefixCut := [⟨64,311966640,311966825⟩]
theorem checked40246 : checkPrefixCuts (2^48) 5279055873 10 Manual.Count131072.C040246.packed 64 cuts40246 = true := by
 decide +kernel
def cuts40247 : List PrefixCut := [⟨14,69366331,69366373⟩,
⟨64,309826191,309826378⟩]
theorem checked40247 : checkPrefixCuts (2^48) 5279186945 10 Manual.Count131072.C040247.packed 64 cuts40247 = true := by
 decide +kernel
def pointBounds40247 : List (Nat × Nat × Nat) := [(5279215616,108943652526368,108944038077981)]
theorem point_links_checked40247 : (cuts40247.take 1).map (fun c => (5279186945-1+2*2^10*c.k,108943583160037+c.lower,108943968711608+c.upper)) = pointBounds40247 := by
 decide +kernel
def cuts40248 : List PrefixCut := [⟨31,149498640,149498730⟩,
⟨64,308485585,308485767⟩]
theorem checked40248 : checkPrefixCuts (2^48) 5279318017 10 Manual.Count131072.C040248.packed 64 cuts40248 = true := by
 decide +kernel
def pointBounds40248 : List (Nat × Nat × Nat) := [(5279381504,108944042484868,108944428036716)]
theorem point_links_checked40248 : (cuts40248.take 1).map (fun c => (5279318017-1+2*2^10*c.k,108943892986228+c.lower,108944278537986+c.upper)) = pointBounds40248 := by
 decide +kernel
def cuts40249 : List PrefixCut := [⟨48,235650996,235651138⟩,
⟨64,313276241,313276428⟩]
theorem checked40249 : checkPrefixCuts (2^48) 5279449089 10 Manual.Count131072.C040249.packed 64 cuts40249 = true := by
 decide +kernel
def pointBounds40249 : List (Nat × Nat × Nat) := [(5279547392,108944437122809,108944822674891)]
theorem point_links_checked40249 : (cuts40249.take 1).map (fun c => (5279449089-1+2*2^10*c.k,108944201471813+c.lower,108944587023753+c.upper)) = pointBounds40249 := by
 decide +kernel
def cuts40250 : List PrefixCut := [⟨64,313641659,313641847⟩]
theorem checked40250 : checkPrefixCuts (2^48) 5279580161 10 Manual.Count131072.C040250.packed 64 cuts40250 = true := by
 decide +kernel
def cuts40251 : List PrefixCut := [⟨1,4904754,4904757⟩,
⟨64,304357628,304357813⟩]
theorem checked40251 : checkPrefixCuts (2^48) 5279711233 10 Manual.Count131072.C040251.packed 64 cuts40251 = true := by
 decide +kernel
def pointBounds40251 : List (Nat × Nat × Nat) := [(5279713280,108944833294467,108945218846785)]
theorem point_links_checked40251 : (cuts40251.take 1).map (fun c => (5279711233-1+2*2^10*c.k,108944828389713+c.lower,108945213942028+c.upper)) = pointBounds40251 := by
 decide +kernel
def cuts40252 : List PrefixCut := [⟨18,86363898,86363950⟩,
⟨64,311280403,311280584⟩]
theorem checked40252 : checkPrefixCuts (2^48) 5279842305 10 Manual.Count131072.C040252.packed 64 cuts40252 = true := by
 decide +kernel
def pointBounds40252 : List (Nat × Nat × Nat) := [(5279879168,108945219111239,108945604663791)]
theorem point_links_checked40252 : (cuts40252.take 1).map (fun c => (5279842305-1+2*2^10*c.k,108945132747341+c.lower,108945518299841+c.upper)) = pointBounds40252 := by
 decide +kernel
def cuts40253 : List PrefixCut := [⟨35,170963714,170963811⟩,
⟨64,312765344,312765525⟩]
theorem checked40253 : checkPrefixCuts (2^48) 5279973377 10 Manual.Count131072.C040253.packed 64 cuts40253 = true := by
 decide +kernel
def pointBounds40253 : List (Nat × Nat × Nat) := [(5280045056,108945614991458,108946000544236)]
theorem point_links_checked40253 : (cuts40253.take 1).map (fun c => (5279973377-1+2*2^10*c.k,108945444027744+c.lower,108945829580425+c.upper)) = pointBounds40253 := by
 decide +kernel
def cuts40254 : List PrefixCut := [⟨52,249428335,249428484⟩,
⟨64,307373463,307373646⟩]
theorem checked40254 : checkPrefixCuts (2^48) 5280104449 10 Manual.Count131072.C040254.packed 64 cuts40254 = true := by
 decide +kernel
def pointBounds40254 : List (Nat × Nat × Nat) := [(5280210944,108946006221423,108946391774434)]
theorem point_links_checked40254 : (cuts40254.take 1).map (fun c => (5280104449-1+2*2^10*c.k,108945756793088+c.lower,108946142345950+c.upper)) = pointBounds40254 := by
 decide +kernel
def cuts40255 : List PrefixCut := [⟨64,310617570,310617753⟩]
theorem checked40255 : checkPrefixCuts (2^48) 5280235521 10 Manual.Count131072.C040255.packed 64 cuts40255 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000007
