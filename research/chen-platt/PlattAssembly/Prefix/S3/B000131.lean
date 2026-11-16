import PlattAssemblyKernel
import PlattCertificates.Count131072.C024192
import PlattCertificates.Count131072.C024193
import PlattCertificates.Count131072.C024194
import PlattCertificates.Count131072.C024195
import PlattCertificates.Count131072.C024196
import PlattCertificates.Count131072.C024197
import PlattCertificates.Count131072.C024198
import PlattCertificates.Count131072.C024199
import PlattCertificates.Count131072.C024200
import PlattCertificates.Count131072.C024201
import PlattCertificates.Count131072.C024202
import PlattCertificates.Count131072.C024203
import PlattCertificates.Count131072.C024204
import PlattCertificates.Count131072.C024205
import PlattCertificates.Count131072.C024206
import PlattCertificates.Count131072.C024207
import PlattCertificates.Count131072.C024208
import PlattCertificates.Count131072.C024209
import PlattCertificates.Count131072.C024210
import PlattCertificates.Count131072.C024211
import PlattCertificates.Count131072.C024212
import PlattCertificates.Count131072.C024213
import PlattCertificates.Count131072.C024214
import PlattCertificates.Count131072.C024215
import PlattCertificates.Count131072.C024216
import PlattCertificates.Count131072.C024217
import PlattCertificates.Count131072.C024218
import PlattCertificates.Count131072.C024219
import PlattCertificates.Count131072.C024220
import PlattCertificates.Count131072.C024221
import PlattCertificates.Count131072.C024222
import PlattCertificates.Count131072.C024223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000131
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24192 : List PrefixCut := [⟨35,140966016,140966097⟩,
⟨128,527595025,527595312⟩]
theorem checked24192 : checkPrefixCuts (2^48) 3174825985 9 Manual.Count131072.C024192.packed 128 cuts24192 = true := by
 decide +kernel
def pointBounds24192 : List (Nat × Nat × Nat) := [(3174861824,102476359043782,102476740822823)]
theorem point_links_checked24192 : (cuts24192.take 1).map (fun c => (3174825985-1+2*2^9*c.k,102476218077766+c.lower,102476599856726+c.upper)) = pointBounds24192 := by
 decide +kernel
def cuts24193 : List PrefixCut := [⟨4,16844383,16844393⟩,
⟨101,424117189,424117429⟩,
⟨128,535640693,535640999⟩]
theorem checked24193 : checkPrefixCuts (2^48) 3174957057 9 Manual.Count131072.C024193.packed 128 cuts24193 = true := by
 decide +kernel
def pointBounds24193 : List (Nat × Nat × Nat) := [(3174961152,102476762517174,102477144296431),(3175060480,102477169789980,102477551569467)]
theorem point_links_checked24193 : (cuts24193.take 2).map (fun c => (3174957057-1+2*2^9*c.k,102476745672791+c.lower,102477127452038+c.upper)) = pointBounds24193 := by
 decide +kernel
def cuts24194 : List PrefixCut := [⟨70,285719148,285719303⟩,
⟨128,529413163,529413450⟩]
theorem checked24194 : checkPrefixCuts (2^48) 3175088129 9 Manual.Count131072.C024194.packed 128 cuts24194 = true := by
 decide +kernel
def pointBounds24194 : List (Nat × Nat × Nat) := [(3175159808,102477567032632,102477948812340)]
theorem point_links_checked24194 : (cuts24194.take 1).map (fun c => (3175088129-1+2*2^9*c.k,102477281313484+c.lower,102477663093037+c.upper)) = pointBounds24194 := by
 decide +kernel
def cuts24195 : List PrefixCut := [⟨39,163464763,163464852⟩,
⟨128,534532711,534533010⟩]
theorem checked24195 : checkPrefixCuts (2^48) 3175219201 9 Manual.Count131072.C024195.packed 128 cuts24195 = true := by
 decide +kernel
def pointBounds24195 : List (Nat × Nat × Nat) := [(3175259136,102477974191410,102478355971339)]
theorem point_links_checked24195 : (cuts24195.take 1).map (fun c => (3175219201-1+2*2^9*c.k,102477810726647+c.lower,102478192506487+c.upper)) = pointBounds24195 := by
 decide +kernel
def cuts24196 : List PrefixCut := [⟨8,35900665,35900685⟩,
⟨105,432042276,432042522⟩,
⟨128,525026055,525026352⟩]
theorem checked24196 : checkPrefixCuts (2^48) 3175350273 9 Manual.Count131072.C024196.packed 128 cuts24196 = true := by
 decide +kernel
def pointBounds24196 : List (Nat × Nat × Nat) := [(3175358464,102478381160023,102478762940182),(3175457792,102478777301634,102479159082019)]
theorem point_links_checked24196 : (cuts24196.take 2).map (fun c => (3175350273-1+2*2^9*c.k,102478345259358+c.lower,102478727039497+c.upper)) = pointBounds24196 := by
 decide +kernel
def cuts24197 : List PrefixCut := [⟨74,303145446,303145618⟩,
⟨128,523852032,523852329⟩]
theorem checked24197 : checkPrefixCuts (2^48) 3175481345 9 Manual.Count131072.C024197.packed 128 cuts24197 = true := by
 decide +kernel
def pointBounds24197 : List (Nat × Nat × Nat) := [(3175557120,102479173430859,102479555211467)]
theorem point_links_checked24197 : (cuts24197.take 1).map (fun c => (3175481345-1+2*2^9*c.k,102478870285413+c.lower,102479252065849+c.upper)) = pointBounds24197 := by
 decide +kernel
def cuts24198 : List PrefixCut := [⟨43,179664762,179664866⟩,
⟨128,528971312,528971613⟩]
theorem checked24198 : checkPrefixCuts (2^48) 3175612417 9 Manual.Count131072.C024198.packed 128 cuts24198 = true := by
 decide +kernel
def pointBounds24198 : List (Nat × Nat × Nat) := [(3175656448,102479573802207,102479955583044)]
theorem point_links_checked24198 : (cuts24198.take 1).map (fun c => (3175612417-1+2*2^9*c.k,102479394137445+c.lower,102479775918178+c.upper)) = pointBounds24198 := by
 decide +kernel
def cuts24199 : List PrefixCut := [⟨12,49988783,49988809⟩,
⟨109,449360184,449360439⟩,
⟨128,528772098,528772400⟩]
theorem checked24199 : checkPrefixCuts (2^48) 3175743489 9 Manual.Count131072.C024199.packed 128 cuts24199 = true := by
 decide +kernel
def pointBounds24199 : List (Nat × Nat × Nat) := [(3175755776,102479973097540,102480354878600),(3175855104,102480372468941,102480754250230)]
theorem point_links_checked24199 : (cuts24199.take 2).map (fun c => (3175743489-1+2*2^9*c.k,102479923108757+c.lower,102480304889791+c.upper)) = pointBounds24199 := by
 decide +kernel
def cuts24200 : List PrefixCut := [⟨78,322871733,322871910⟩,
⟨128,528307147,528307439⟩]
theorem checked24200 : checkPrefixCuts (2^48) 3175874561 9 Manual.Count131072.C024200.packed 128 cuts24200 = true := by
 decide +kernel
def pointBounds24200 : List (Nat × Nat × Nat) := [(3175954432,102480774752588,102481156534101)]
theorem point_links_checked24200 : (cuts24200.take 1).map (fun c => (3175874561-1+2*2^9*c.k,102480451880855+c.lower,102480833662191+c.upper)) = pointBounds24200 := by
 decide +kernel
def cuts24201 : List PrefixCut := [⟨47,193113363,193113475⟩,
⟨128,533779900,533780202⟩]
theorem checked24201 : checkPrefixCuts (2^48) 3176005633 9 Manual.Count131072.C024201.packed 128 cuts24201 = true := by
 decide +kernel
def pointBounds24201 : List (Nat × Nat × Nat) := [(3176053760,102481173301365,102481555083105)]
theorem point_links_checked24201 : (cuts24201.take 1).map (fun c => (3176005633-1+2*2^9*c.k,102480980188002+c.lower,102481361969630+c.upper)) = pointBounds24201 := by
 decide +kernel
def cuts24202 : List PrefixCut := [⟨16,68061353,68061392⟩,
⟨113,470750442,470750705⟩,
⟨128,532074336,532074636⟩]
theorem checked24202 : checkPrefixCuts (2^48) 3176136705 9 Manual.Count131072.C024202.packed 128 cuts24202 = true := by
 decide +kernel
def pointBounds24202 : List (Nat × Nat × Nat) := [(3176153088,102481582029255,102481963811224),(3176252416,102481984718344,102482366500537)]
theorem point_links_checked24202 : (cuts24202.take 2).map (fun c => (3176136705-1+2*2^9*c.k,102481513967902+c.lower,102481895749832+c.upper)) = pointBounds24202 := by
 decide +kernel
def cuts24203 : List PrefixCut := [⟨82,343302140,343302332⟩,
⟨128,535862829,535863129⟩]
theorem checked24203 : checkPrefixCuts (2^48) 3176267777 9 Manual.Count131072.C024203.packed 128 cuts24203 = true := by
 decide +kernel
def pointBounds24203 : List (Nat × Nat × Nat) := [(3176351744,102482389344378,102482771126800)]
theorem point_links_checked24203 : (cuts24203.take 1).map (fun c => (3176267777-1+2*2^9*c.k,102482046042238+c.lower,102482427824468+c.upper)) = pointBounds24203 := by
 decide +kernel
def cuts24204 : List PrefixCut := [⟨51,214622517,214622632⟩,
⟨128,532207637,532207929⟩]
theorem checked24204 : checkPrefixCuts (2^48) 3176398849 9 Manual.Count131072.C024204.packed 128 cuts24204 = true := by
 decide +kernel
def pointBounds24204 : List (Nat × Nat × Nat) := [(3176451072,102482796527584,102483178310229)]
theorem point_links_checked24204 : (cuts24204.take 1).map (fun c => (3176398849-1+2*2^9*c.k,102482581905067+c.lower,102482963687597+c.upper)) = pointBounds24204 := by
 decide +kernel
def cuts24205 : List PrefixCut := [⟨20,82141956,82142001⟩,
⟨117,482033764,482034036⟩,
⟨128,526337416,526337716⟩]
theorem checked24205 : checkPrefixCuts (2^48) 3176529921 9 Manual.Count131072.C024205.packed 128 cuts24205 = true := by
 decide +kernel
def pointBounds24205 : List (Nat × Nat × Nat) := [(3176550400,102483196254660,102483578037527),(3176649728,102483596146468,102483977929562)]
theorem point_links_checked24205 : (cuts24205.take 2).map (fun c => (3176529921-1+2*2^9*c.k,102483114112704+c.lower,102483495895526+c.upper)) = pointBounds24205 := by
 decide +kernel
def cuts24206 : List PrefixCut := [⟨86,360537495,360537701⟩,
⟨128,533404111,533404416⟩]
theorem checked24206 : checkPrefixCuts (2^48) 3176660993 9 Manual.Count131072.C024206.packed 128 cuts24206 = true := by
 decide +kernel
def pointBounds24206 : List (Nat × Nat × Nat) := [(3176749056,102484000987615,102484382770943)]
theorem point_links_checked24206 : (cuts24206.take 1).map (fun c => (3176660993-1+2*2^9*c.k,102483640450120+c.lower,102484022233242+c.upper)) = pointBounds24206 := by
 decide +kernel
def cuts24207 : List PrefixCut := [⟨55,226557112,226557241⟩,
⟨128,528508930,528509231⟩]
theorem checked24207 : checkPrefixCuts (2^48) 3176792065 9 Manual.Count131072.C024207.packed 128 cuts24207 = true := by
 decide +kernel
def pointBounds24207 : List (Nat × Nat × Nat) := [(3176848384,102484400411343,102484782194899)]
theorem point_links_checked24207 : (cuts24207.take 1).map (fun c => (3176792065-1+2*2^9*c.k,102484173854231+c.lower,102484555637658+c.upper)) = pointBounds24207 := by
 decide +kernel
def cuts24208 : List PrefixCut := [⟨24,98168254,98168305⟩,
⟨121,501376779,501377054⟩,
⟨128,531056536,531056829⟩]
theorem checked24208 : checkPrefixCuts (2^48) 3176923137 9 Manual.Count131072.C024208.packed 128 cuts24208 = true := by
 decide +kernel
def pointBounds24208 : List (Nat × Nat × Nat) := [(3176947712,102484800531415,102485182315194),(3177047040,102485203739940,102485585523943)]
theorem point_links_checked24208 : (cuts24208.take 2).map (fun c => (3176923137-1+2*2^9*c.k,102484702363161+c.lower,102485084146889+c.upper)) = pointBounds24208 := by
 decide +kernel
def cuts24209 : List PrefixCut := [⟨90,371921321,371921539⟩,
⟨128,533603711,533604023⟩]
theorem checked24209 : checkPrefixCuts (2^48) 3177054209 9 Manual.Count131072.C024209.packed 128 cuts24209 = true := by
 decide +kernel
def pointBounds24209 : List (Nat × Nat × Nat) := [(3177146368,102485605341018,102485987125257)]
theorem point_links_checked24209 : (cuts24209.take 1).map (fun c => (3177054209-1+2*2^9*c.k,102485233419697+c.lower,102485615203718+c.upper)) = pointBounds24209 := by
 decide +kernel
def cuts24210 : List PrefixCut := [⟨59,247347986,247348124⟩,
⟨128,534910662,534910964⟩]
theorem checked24210 : checkPrefixCuts (2^48) 3177185281 9 Manual.Count131072.C024210.packed 128 cuts24210 = true := by
 decide +kernel
def pointBounds24210 : List (Nat × Nat × Nat) := [(3177245696,102486014371394,102486396155865)]
theorem point_links_checked24210 : (cuts24210.take 1).map (fun c => (3177185281-1+2*2^9*c.k,102485767023408+c.lower,102486148807741+c.upper)) = pointBounds24210 := by
 decide +kernel
def cuts24211 : List PrefixCut := [⟨28,114013374,114013436⟩,
⟨125,511944830,511945122⟩,
⟨128,524081011,524081310⟩]
theorem checked24211 : checkPrefixCuts (2^48) 3177316353 9 Manual.Count131072.C024211.packed 128 cuts24211 = true := by
 decide +kernel
def pointBounds24211 : List (Nat × Nat × Nat) := [(3177345024,102486415947444,102486797732141),(3177444352,102486813878900,102487195663827)]
theorem point_links_checked24211 : (cuts24211.take 2).map (fun c => (3177316353-1+2*2^9*c.k,102486301934070+c.lower,102486683718705+c.upper)) = pointBounds24211 := by
 decide +kernel
def cuts24212 : List PrefixCut := [⟨94,391097790,391098015⟩,
⟨128,532474748,532475054⟩]
theorem checked24212 : checkPrefixCuts (2^48) 3177447425 9 Manual.Count131072.C024212.packed 128 cuts24212 = true := by
 decide +kernel
def pointBounds24212 : List (Nat × Nat × Nat) := [(3177543680,102487217112871,102487598898030)]
theorem point_links_checked24212 : (cuts24212.take 1).map (fun c => (3177447425-1+2*2^9*c.k,102486826015081+c.lower,102487207800015+c.upper)) = pointBounds24212 := by
 decide +kernel
def cuts24213 : List PrefixCut := [⟨63,258301281,258301427⟩,
⟨128,526429480,526429777⟩]
theorem checked24213 : checkPrefixCuts (2^48) 3177578497 9 Manual.Count131072.C024213.packed 128 cuts24213 = true := by
 decide +kernel
def pointBounds24213 : List (Nat × Nat × Nat) := [(3177643008,102487616791110,102487998576496)]
theorem point_links_checked24213 : (cuts24213.take 1).map (fun c => (3177578497-1+2*2^9*c.k,102487358489829+c.lower,102487740275069+c.upper)) = pointBounds24213 := by
 decide +kernel
def cuts24214 : List PrefixCut := [⟨32,129234515,129234590⟩,
⟨128,529773574,529773875⟩]
theorem checked24214 : checkPrefixCuts (2^48) 3177709569 9 Manual.Count131072.C024214.packed 128 cuts24214 = true := by
 decide +kernel
def pointBounds24214 : List (Nat × Nat × Nat) := [(3177742336,102488014153824,102488395939436)]
theorem point_links_checked24214 : (cuts24214.take 1).map (fun c => (3177709569-1+2*2^9*c.k,102487884919309+c.lower,102488266704846+c.upper)) = pointBounds24214 := by
 decide +kernel
def cuts24215 : List PrefixCut := [⟨1,4162990,4162992⟩,
⟨98,407435177,407435405⟩,
⟨128,530371776,530372074⟩]
theorem checked24215 : checkPrefixCuts (2^48) 3177840641 9 Manual.Count131072.C024215.packed 128 cuts24215 = true := by
 decide +kernel
def pointBounds24215 : List (Nat × Nat × Nat) := [(3177841664,102488418855873,102488800641713),(3177940992,102488822128060,102489203914126)]
theorem point_links_checked24215 : (cuts24215.take 2).map (fun c => (3177840641-1+2*2^9*c.k,102488414692883+c.lower,102488796478721+c.upper)) = pointBounds24215 := by
 decide +kernel
def cuts24216 : List PrefixCut := [⟨67,277665836,277665992⟩,
⟨128,527072851,527073150⟩]
theorem checked24216 : checkPrefixCuts (2^48) 3177971713 9 Manual.Count131072.C024216.packed 128 cuts24216 = true := by
 decide +kernel
def pointBounds24216 : List (Nat × Nat × Nat) := [(3178040320,102489222730495,102489604516787)]
theorem point_links_checked24216 : (cuts24216.take 1).map (fun c => (3177971713-1+2*2^9*c.k,102488945064659+c.lower,102489326850795+c.upper)) = pointBounds24216 := by
 decide +kernel
def cuts24217 : List PrefixCut := [⟨36,148614475,148614562⟩,
⟨128,536793167,536793479⟩]
theorem checked24217 : checkPrefixCuts (2^48) 3178102785 9 Manual.Count131072.C024217.packed 128 cuts24217 = true := by
 decide +kernel
def pointBounds24217 : List (Nat × Nat × Nat) := [(3178139648,102489620751985,102490002538507)]
theorem point_links_checked24217 : (cuts24217.take 1).map (fun c => (3178102785-1+2*2^9*c.k,102489472137510+c.lower,102489853923945+c.upper)) = pointBounds24217 := by
 decide +kernel
def cuts24218 : List PrefixCut := [⟨5,19838164,19838177⟩,
⟨102,415709257,415709500⟩,
⟨128,523044001,523044308⟩]
theorem checked24218 : checkPrefixCuts (2^48) 3178233857 9 Manual.Count131072.C024218.packed 128 cuts24218 = true := by
 decide +kernel
def pointBounds24218 : List (Nat × Nat × Nat) := [(3178238976,102490028768841,102490410555601),(3178338304,102490424639934,102490806426924)]
theorem point_links_checked24218 : (cuts24218.take 2).map (fun c => (3178233857-1+2*2^9*c.k,102490008930677+c.lower,102490390717424+c.upper)) = pointBounds24218 := by
 decide +kernel
def cuts24219 : List PrefixCut := [⟨71,289321111,289321268⟩,
⟨128,530992669,530992958⟩]
theorem checked24219 : checkPrefixCuts (2^48) 3178364929 9 Manual.Count131072.C024219.packed 128 cuts24219 = true := by
 decide +kernel
def pointBounds24219 : List (Nat × Nat × Nat) := [(3178437632,102490821295789,102491203083000)]
theorem point_links_checked24219 : (cuts24219.take 1).map (fun c => (3178364929-1+2*2^9*c.k,102490531974678+c.lower,102490913761732+c.upper)) = pointBounds24219 := by
 decide +kernel
def cuts24220 : List PrefixCut := [⟨40,167901089,167901182⟩,
⟨128,533538955,533539250⟩]
theorem checked24220 : checkPrefixCuts (2^48) 3178496001 9 Manual.Count131072.C024220.packed 128 cuts24220 = true := by
 decide +kernel
def pointBounds24220 : List (Nat × Nat × Nat) := [(3178536960,102491230868436,102491612655872)]
theorem point_links_checked24220 : (cuts24220.take 1).map (fun c => (3178496001-1+2*2^9*c.k,102491062967347+c.lower,102491444754690+c.upper)) = pointBounds24220 := by
 decide +kernel
def cuts24221 : List PrefixCut := [⟨10,43213478,43213502⟩,
⟨108,447978553,447978799⟩,
⟨128,533516875,533517170⟩]
theorem checked24221 : checkPrefixCuts (2^48) 3178627073 9 Manual.Count131072.C024221.packed 128 cuts24221 = true := by
 decide +kernel
def pointBounds24221 : List (Nat × Nat × Nat) := [(3178637312,102491639719780,102492021507442),(3178737664,102492044484855,102492426272739)]
theorem point_links_checked24221 : (cuts24221.take 2).map (fun c => (3178627073-1+2*2^9*c.k,102491596506302+c.lower,102491978293940+c.upper)) = pointBounds24221 := by
 decide +kernel
def cuts24222 : List PrefixCut := [⟨78,323907118,323907302⟩,
⟨128,541375508,541375814⟩]
theorem checked24222 : checkPrefixCuts (2^48) 3178758145 9 Manual.Count131072.C024222.packed 128 cuts24222 = true := by
 decide +kernel
def pointBounds24222 : List (Nat × Nat × Nat) := [(3178838016,102492453930295,102492835718412)]
theorem point_links_checked24222 : (cuts24222.take 1).map (fun c => (3178758145-1+2*2^9*c.k,102492130023177+c.lower,102492511811110+c.upper)) = pointBounds24222 := by
 decide +kernel
def cuts24223 : List PrefixCut := [⟨48,203474970,203475079⟩,
⟨128,535775130,535775428⟩]
theorem checked24223 : checkPrefixCuts (2^48) 3178889217 9 Manual.Count131072.C024223.packed 128 cuts24223 = true := by
 decide +kernel
def pointBounds24223 : List (Nat × Nat × Nat) := [(3178938368,102492874873655,102493256662003)]
theorem point_links_checked24223 : (cuts24223.take 1).map (fun c => (3178889217-1+2*2^9*c.k,102492671398685+c.lower,102493053186924+c.upper)) = pointBounds24223 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000131
