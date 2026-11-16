import PlattAssemblyKernel
import PlattCertificates.Count131072.C018192
import PlattCertificates.Count131072.C018193
import PlattCertificates.Count131072.C018194
import PlattCertificates.Count131072.C018195
import PlattCertificates.Count131072.C018196
import PlattCertificates.Count131072.C018197
import PlattCertificates.Count131072.C018198
import PlattCertificates.Count131072.C018199
import PlattCertificates.Count131072.C018200
import PlattCertificates.Count131072.C018201
import PlattCertificates.Count131072.C018202
import PlattCertificates.Count131072.C018203
import PlattCertificates.Count131072.C018204
import PlattCertificates.Count131072.C018205
import PlattCertificates.Count131072.C018206
import PlattCertificates.Count131072.C018207
import PlattCertificates.Count131072.C018208
import PlattCertificates.Count131072.C018209
import PlattCertificates.Count131072.C018210
import PlattCertificates.Count131072.C018211
import PlattCertificates.Count131072.C018212
import PlattCertificates.Count131072.C018213
import PlattCertificates.Count131072.C018214
import PlattCertificates.Count131072.C018215
import PlattCertificates.Count131072.C018216
import PlattCertificates.Count131072.C018217
import PlattCertificates.Count131072.C018218
import PlattCertificates.Count131072.C018219
import PlattCertificates.Count131072.C018220
import PlattCertificates.Count131072.C018221
import PlattCertificates.Count131072.C018222
import PlattCertificates.Count131072.C018223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000256
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18192 : List PrefixCut := [⟨57,317604831,317605022⟩,
⟨128,715100850,715101285⟩]
theorem checked18192 : checkPrefixCuts (2^48) 2388393985 9 Manual.Count131072.C018192.packed 128 cuts18192 = true := by
 decide +kernel
def pointBounds18192 : List (Nat × Nat × Nat) := [(2388452352,98790674929441,98791054564291)]
theorem point_links_checked18192 : (cuts18192.take 1).map (fun c => (2388393985-1+2*2^9*c.k,98790357324610+c.lower,98790736959269+c.upper)) = pointBounds18192 := by
 decide +kernel
def cuts18193 : List PrefixCut := [⟨2,10841703,10841709⟩,
⟨75,417752578,417752835⟩,
⟨128,710701635,710702069⟩]
theorem checked18193 : checkPrefixCuts (2^48) 2388525057 9 Manual.Count131072.C018193.packed 128 cuts18193 = true := by
 decide +kernel
def pointBounds18193 : List (Nat × Nat × Nat) := [(2388527104,98791083267163,98791462902263),(2388601856,98791490178038,98791869813389)]
theorem point_links_checked18193 : (cuts18193.take 2).map (fun c => (2388525057-1+2*2^9*c.k,98791072425460+c.lower,98791452060554+c.upper)) = pointBounds18193 := by
 decide +kernel
def cuts18194 : List PrefixCut := [⟨20,106996608,106996671⟩,
⟨93,512703603,512703915⟩,
⟨128,710073197,710073631⟩]
theorem checked18194 : checkPrefixCuts (2^48) 2388656129 9 Manual.Count131072.C018194.packed 128 cuts18194 = true := by
 decide +kernel
def pointBounds18194 : List (Nat × Nat × Nat) := [(2388676608,98791890123703,98792269759294),(2388751360,98792295830698,98792675466538)]
theorem point_links_checked18194 : (cuts18194.take 2).map (fun c => (2388656129-1+2*2^9*c.k,98791783127095+c.lower,98792162762623+c.upper)) = pointBounds18194 := by
 decide +kernel
def cuts18195 : List PrefixCut := [⟨38,214334116,214334242⟩,
⟨111,624964536,624964910⟩,
⟨128,720049859,720050291⟩]
theorem checked18195 : checkPrefixCuts (2^48) 2388787201 9 Manual.Count131072.C018195.packed 128 cuts18195 = true := by
 decide +kernel
def pointBounds18195 : List (Nat × Nat × Nat) := [(2388826112,98792707534408,98793087170496),(2388900864,98793118164828,98793497801164)]
theorem point_links_checked18195 : (cuts18195.take 2).map (fun c => (2388787201-1+2*2^9*c.k,98792493200292+c.lower,98792872836254+c.upper)) = pointBounds18195 := by
 decide +kernel
def cuts18196 : List PrefixCut := [⟨56,308462795,308462983⟩,
⟨128,711409278,711409715⟩]
theorem checked18196 : checkPrefixCuts (2^48) 2388918273 9 Manual.Count131072.C018196.packed 128 cuts18196 = true := by
 decide +kernel
def pointBounds18196 : List (Nat × Nat × Nat) := [(2388975616,98793521712946,98793901349528)]
theorem point_links_checked18196 : (cuts18196.take 1).map (fun c => (2388918273-1+2*2^9*c.k,98793213250151+c.lower,98793592886545+c.upper)) = pointBounds18196 := by
 decide +kernel
def cuts18197 : List PrefixCut := [⟨1,6244394,6244398⟩,
⟨74,418839121,418839377⟩,
⟨128,729042514,729042958⟩]
theorem checked18197 : checkPrefixCuts (2^48) 2389049345 9 Manual.Count131072.C018197.packed 128 cuts18197 = true := by
 decide +kernel
def pointBounds18197 : List (Nat × Nat × Nat) := [(2389050368,98793930903823,98794310540658),(2389125120,98794343498550,98794723135637)]
theorem point_links_checked18197 : (cuts18197.take 2).map (fun c => (2389049345-1+2*2^9*c.k,98793924659429+c.lower,98794304296260+c.upper)) = pointBounds18197 := by
 decide +kernel
def cuts18198 : List PrefixCut := [⟨19,106501907,106501972⟩,
⟨92,510706349,510706660⟩,
⟨128,713098390,713098826⟩]
theorem checked18198 : checkPrefixCuts (2^48) 2389180417 9 Manual.Count131072.C018198.packed 128 cuts18198 = true := by
 decide +kernel
def pointBounds18198 : List (Nat × Nat × Nat) := [(2389199872,98794760203850,98795139841190),(2389274624,98795164408292,98795544045878)]
theorem point_links_checked18198 : (cuts18198.take 2).map (fun c => (2389180417-1+2*2^9*c.k,98794653701943+c.lower,98795033339218+c.upper)) = pointBounds18198 := by
 decide +kernel
def cuts18199 : List PrefixCut := [⟨37,202506664,202506787⟩,
⟨110,617052460,617052827⟩,
⟨128,721069725,721070151⟩]
theorem checked18199 : checkPrefixCuts (2^48) 2389311489 9 Manual.Count131072.C018199.packed 128 cuts18199 = true := by
 decide +kernel
def pointBounds18199 : List (Nat × Nat × Nat) := [(2389349376,98795569306997,98795948944831),(2389424128,98795983852793,98796363490871)]
theorem point_links_checked18199 : (cuts18199.take 2).map (fun c => (2389311489-1+2*2^9*c.k,98795366800333+c.lower,98795746438044+c.upper)) = pointBounds18199 := by
 decide +kernel
def cuts18200 : List PrefixCut := [⟨55,303094280,303094462⟩,
⟨128,711253184,711253616⟩]
theorem checked18200 : checkPrefixCuts (2^48) 2389442561 9 Manual.Count131072.C018200.packed 128 cuts18200 = true := by
 decide +kernel
def pointBounds18200 : List (Nat × Nat × Nat) := [(2389498880,98796390964338,98796770602657),(2389573632,98796799123242,98797178761811)]
theorem point_links_checked18200 : (cuts18200.take 2).map (fun c => (2389442561-1+2*2^9*c.k,98796087870058+c.lower,98796467508195+c.upper)) = pointBounds18200 := by
 decide +kernel
def cuts18201 : List PrefixCut := [⟨73,407675056,407675306⟩,
⟨128,717221553,717221992⟩]
theorem checked18201 : checkPrefixCuts (2^48) 2389573633 9 Manual.Count131072.C018201.packed 128 cuts18201 = true := by
 decide +kernel
def pointBounds18201 : List (Nat × Nat × Nat) := [(2389648384,98797206798298,98797586437117)]
theorem point_links_checked18201 : (cuts18201.take 1).map (fun c => (2389573633-1+2*2^9*c.k,98796799123242+c.lower,98797178761811+c.upper)) = pointBounds18201 := by
 decide +kernel
def cuts18202 : List PrefixCut := [⟨18,101413756,101413818⟩,
⟨91,507532013,507532327⟩,
⟨128,708112944,708113383⟩]
theorem checked18202 : checkPrefixCuts (2^48) 2389704705 9 Manual.Count131072.C018202.packed 128 cuts18202 = true := by
 decide +kernel
def pointBounds18202 : List (Nat × Nat × Nat) := [(2389723136,98797617758551,98797997397621),(2389797888,98798023876808,98798403516130)]
theorem point_links_checked18202 : (cuts18202.take 2).map (fun c => (2389704705-1+2*2^9*c.k,98797516344795+c.lower,98797895983803+c.upper)) = pointBounds18202 := by
 decide +kernel
def cuts18203 : List PrefixCut := [⟨36,201637827,201637951⟩,
⟨109,608084032,608084399⟩,
⟨128,713138466,713138894⟩]
theorem checked18203 : checkPrefixCuts (2^48) 2389835777 9 Manual.Count131072.C018203.packed 128 cuts18203 = true := by
 decide +kernel
def pointBounds18203 : List (Nat × Nat × Nat) := [(2389872640,98798426095566,98798805735137),(2389947392,98798832541771,98799212181585)]
theorem point_links_checked18203 : (cuts18203.take 2).map (fun c => (2389835777-1+2*2^9*c.k,98798224457739+c.lower,98798604097186+c.upper)) = pointBounds18203 := by
 decide +kernel
def cuts18204 : List PrefixCut := [⟨54,307620987,307621171⟩,
⟨127,720165721,720166153⟩,
⟨128,726171844,726172280⟩]
theorem checked18204 : checkPrefixCuts (2^48) 2389966849 9 Manual.Count131072.C018204.packed 128 cuts18204 = true := by
 decide +kernel
def pointBounds18204 : List (Nat × Nat × Nat) := [(2390022144,98799245217192,98799624857251),(2390096896,98799657761926,98800037402233)]
theorem point_links_checked18204 : (cuts18204.take 2).map (fun c => (2389966849-1+2*2^9*c.k,98798937596205+c.lower,98799317236080+c.upper)) = pointBounds18204 := by
 decide +kernel
def cuts18205 : List PrefixCut := [⟨72,397222257,397222500⟩,
⟨128,702225989,702226420⟩]
theorem checked18205 : checkPrefixCuts (2^48) 2390097921 9 Manual.Count131072.C018205.packed 128 cuts18205 = true := by
 decide +kernel
def pointBounds18205 : List (Nat × Nat × Nat) := [(2390171648,98800060990306,98800440630860)]
theorem point_links_checked18205 : (cuts18205.take 1).map (fun c => (2390097921-1+2*2^9*c.k,98799663768049+c.lower,98800043408360+c.upper)) = pointBounds18205 := by
 decide +kernel
def cuts18206 : List PrefixCut := [⟨17,94914733,94914790⟩,
⟨90,504476936,504477244⟩,
⟨128,719144529,719144969⟩]
theorem checked18206 : checkPrefixCuts (2^48) 2390228993 9 Manual.Count131072.C018206.packed 128 cuts18206 = true := by
 decide +kernel
def pointBounds18206 : List (Nat × Nat × Nat) := [(2390246400,98800460908771,98800840549570),(2390321152,98800870470974,98801250112024)]
theorem point_links_checked18206 : (cuts18206.take 2).map (fun c => (2390228993-1+2*2^9*c.k,98800365994038+c.lower,98800745634780+c.upper)) = pointBounds18206 := by
 decide +kernel
def cuts18207 : List PrefixCut := [⟨35,200180590,200180710⟩,
⟨108,615604586,615604957⟩,
⟨128,725816934,725817370⟩]
theorem checked18207 : checkPrefixCuts (2^48) 2390360065 9 Manual.Count131072.C018207.packed 128 cuts18207 = true := by
 decide +kernel
def pointBounds18207 : List (Nat × Nat × Nat) := [(2390395904,98801285319157,98801664960459),(2390470656,98801700743153,98802080384706)]
theorem point_links_checked18207 : (cuts18207.take 2).map (fun c => (2390360065-1+2*2^9*c.k,98801085138567+c.lower,98801464779749+c.upper)) = pointBounds18207 := by
 decide +kernel
def cuts18208 : List PrefixCut := [⟨53,289302864,289303043⟩,
⟨126,692102420,692102838⟩,
⟨128,702816880,702817305⟩]
theorem checked18208 : checkPrefixCuts (2^48) 2390491137 9 Manual.Count131072.C018208.packed 128 cuts18208 = true := by
 decide +kernel
def pointBounds18208 : List (Nat × Nat × Nat) := [(2390545408,98802100258365,98802479900162),(2390620160,98802503057921,98802882699957)]
theorem point_links_checked18208 : (cuts18208.take 2).map (fun c => (2390491137-1+2*2^9*c.k,98801810955501+c.lower,98802190597119+c.upper)) = pointBounds18208 := by
 decide +kernel
def cuts18209 : List PrefixCut := [⟨71,395251392,395251630⟩,
⟨128,711137738,711138169⟩]
theorem checked18209 : checkPrefixCuts (2^48) 2390622209 9 Manual.Count131072.C018209.packed 128 cuts18209 = true := by
 decide +kernel
def pointBounds18209 : List (Nat × Nat × Nat) := [(2390694912,98802909023773,98803288666054)]
theorem point_links_checked18209 : (cuts18209.take 1).map (fun c => (2390622209-1+2*2^9*c.k,98802513772381+c.lower,98802893414424+c.upper)) = pointBounds18209 := by
 decide +kernel
def cuts18210 : List PrefixCut := [⟨16,92656983,92657040⟩,
⟨89,504601815,504602121⟩,
⟨128,722872009,722872453⟩]
theorem checked18210 : checkPrefixCuts (2^48) 2390753281 9 Manual.Count131072.C018210.packed 128 cuts18210 = true := by
 decide +kernel
def pointBounds18210 : List (Nat × Nat × Nat) := [(2390769664,98803317567102,98803697209633),(2390844416,98803729511934,98804109154714)]
theorem point_links_checked18210 : (cuts18210.take 2).map (fun c => (2390753281-1+2*2^9*c.k,98803224910119+c.lower,98803604552593+c.upper)) = pointBounds18210 := by
 decide +kernel
def cuts18211 : List PrefixCut := [⟨34,190012201,190012314⟩,
⟨107,597575500,597575859⟩,
⟨128,717416942,717417373⟩]
theorem checked18211 : checkPrefixCuts (2^48) 2390884353 9 Manual.Count131072.C018211.packed 128 cuts18211 = true := by
 decide +kernel
def pointBounds18211 : List (Nat × Nat × Nat) := [(2390919168,98804137794329,98804517437360),(2390993920,98804545357628,98804925000905)]
theorem point_links_checked18211 : (cuts18211.take 2).map (fun c => (2390884353-1+2*2^9*c.k,98803947782128+c.lower,98804327425046+c.upper)) = pointBounds18211 := by
 decide +kernel
def cuts18212 : List PrefixCut := [⟨52,289592665,289592838⟩,
⟨125,702310118,702310540⟩,
⟨128,718201713,718202145⟩]
theorem checked18212 : checkPrefixCuts (2^48) 2391015425 9 Manual.Count131072.C018212.packed 128 cuts18212 = true := by
 decide +kernel
def pointBounds18212 : List (Nat × Nat × Nat) := [(2391068672,98804954791735,98805334435257),(2391143424,98805367509188,98805747152959)]
theorem point_links_checked18212 : (cuts18212.take 2).map (fun c => (2391015425-1+2*2^9*c.k,98804665199070+c.lower,98805044842419+c.upper)) = pointBounds18212 := by
 decide +kernel
def cuts18213 : List PrefixCut := [⟨70,386807234,386807469⟩,
⟨128,717691335,717691772⟩]
theorem checked18213 : checkPrefixCuts (2^48) 2391146497 9 Manual.Count131072.C018213.packed 128 cuts18213 = true := by
 decide +kernel
def pointBounds18213 : List (Nat × Nat × Nat) := [(2391218176,98805770208017,98806149852033)]
theorem point_links_checked18213 : (cuts18213.take 1).map (fun c => (2391146497-1+2*2^9*c.k,98805383400783+c.lower,98805763044564+c.upper)) = pointBounds18213 := by
 decide +kernel
def cuts18214 : List PrefixCut := [⟨15,82042911,82042961⟩,
⟨88,490484163,490484462⟩,
⟨128,715651057,715651496⟩]
theorem checked18214 : checkPrefixCuts (2^48) 2391277569 9 Manual.Count131072.C018214.packed 128 cuts18214 = true := by
 decide +kernel
def pointBounds18214 : List (Nat × Nat × Nat) := [(2391292928,98806183135029,98806562779297),(2391367680,98806591576281,98806971220798)]
theorem point_links_checked18214 : (cuts18214.take 2).map (fun c => (2391277569-1+2*2^9*c.k,98806101092118+c.lower,98806480736336+c.upper)) = pointBounds18214 := by
 decide +kernel
def cuts18215 : List PrefixCut := [⟨33,188558141,188558255⟩,
⟨106,592972114,592972472⟩,
⟨128,714905839,714906268⟩]
theorem checked18215 : checkPrefixCuts (2^48) 2391408641 9 Manual.Count131072.C018215.packed 128 cuts18215 = true := by
 decide +kernel
def pointBounds18215 : List (Nat × Nat × Nat) := [(2391442432,98807005301316,98807384946087),(2391517184,98807409715289,98807789360304)]
theorem point_links_checked18215 : (cuts18215.take 2).map (fun c => (2391408641-1+2*2^9*c.k,98806816743175+c.lower,98807196387832+c.upper)) = pointBounds18215 := by
 decide +kernel
def cuts18216 : List PrefixCut := [⟨51,285056854,285057028⟩,
⟨124,685914723,685915141⟩,
⟨128,709334983,709335415⟩]
theorem checked18216 : checkPrefixCuts (2^48) 2391539713 9 Manual.Count131072.C018216.packed 128 cuts18216 = true := by
 decide +kernel
def pointBounds18216 : List (Nat × Nat × Nat) := [(2391591936,98807816705868,98808196351128),(2391666688,98808217563737,98808597209241)]
theorem point_links_checked18216 : (cuts18216.take 2).map (fun c => (2391539713-1+2*2^9*c.k,98807531649014+c.lower,98807911294100+c.upper)) = pointBounds18216 := by
 decide +kernel
def cuts18217 : List PrefixCut := [⟨69,389664691,389664930⟩,
⟨128,708943303,708943740⟩]
theorem checked18217 : checkPrefixCuts (2^48) 2391670785 9 Manual.Count131072.C018217.packed 128 cuts18217 = true := by
 decide +kernel
def pointBounds18217 : List (Nat × Nat × Nat) := [(2391741440,98808630648688,98809010294445)]
theorem point_links_checked18217 : (cuts18217.take 1).map (fun c => (2391670785-1+2*2^9*c.k,98808240983997+c.lower,98808620629515+c.upper)) = pointBounds18217 := by
 decide +kernel
def cuts18218 : List PrefixCut := [⟨14,77670674,77670721⟩,
⟨87,479667827,479668117⟩,
⟨128,710080954,710081383⟩]
theorem checked18218 : checkPrefixCuts (2^48) 2391801857 9 Manual.Count131072.C018218.packed 128 cuts18218 = true := by
 decide +kernel
def pointBounds18218 : List (Nat × Nat × Nat) := [(2391816192,98809027597974,98809407243976),(2391890944,98809429595127,98809809241372)]
theorem point_links_checked18218 : (cuts18218.take 2).map (fun c => (2391801857-1+2*2^9*c.k,98808949927300+c.lower,98809329573255+c.upper)) = pointBounds18218 := by
 decide +kernel
def cuts18219 : List PrefixCut := [⟨32,175572489,175572595⟩,
⟨105,584840170,584840523⟩,
⟨128,711807053,711807486⟩]
theorem checked18219 : checkPrefixCuts (2^48) 2391932929 9 Manual.Count131072.C018219.packed 128 cuts18219 = true := by
 decide +kernel
def pointBounds18219 : List (Nat × Nat × Nat) := [(2391965696,98809835580743,98810215227233),(2392040448,98810244848424,98810624495161)]
theorem point_links_checked18219 : (cuts18219.take 2).map (fun c => (2391932929-1+2*2^9*c.k,98809660008254+c.lower,98810039654638+c.upper)) = pointBounds18219 := by
 decide +kernel
def cuts18220 : List PrefixCut := [⟨50,277581283,277581456⟩,
⟨124,692236014,692236433⟩,
⟨128,712003559,712003990⟩]
theorem checked18220 : checkPrefixCuts (2^48) 2392064001 9 Manual.Count131072.C018220.packed 128 cuts18220 = true := by
 decide +kernel
def pointBounds18220 : List (Nat × Nat × Nat) := [(2392115200,98810649396590,98811029043580),(2392190976,98811064051321,98811443698557)]
theorem point_links_checked18220 : (cuts18220.take 2).map (fun c => (2392064001-1+2*2^9*c.k,98810371815307+c.lower,98810751462124+c.upper)) = pointBounds18220 := by
 decide +kernel
def cuts18221 : List PrefixCut := [⟨70,399462769,399463011⟩,
⟨128,724907194,724907631⟩]
theorem checked18221 : checkPrefixCuts (2^48) 2392195073 9 Manual.Count131072.C018221.packed 128 cuts18221 = true := by
 decide +kernel
def pointBounds18221 : List (Nat × Nat × Nat) := [(2392266752,98811483281635,98811862929125)]
theorem point_links_checked18221 : (cuts18221.take 1).map (fun c => (2392195073-1+2*2^9*c.k,98811083818866+c.lower,98811463466114+c.upper)) = pointBounds18221 := by
 decide +kernel
def cuts18222 : List PrefixCut := [⟨16,86477893,86477947⟩,
⟨90,497092877,497093185⟩,
⟨128,710984060,710984499⟩]
theorem checked18222 : checkPrefixCuts (2^48) 2392326145 9 Manual.Count131072.C018222.packed 128 cuts18222 = true := by
 decide +kernel
def pointBounds18222 : List (Nat × Nat × Nat) := [(2392342528,98811895203953,98812274851692),(2392418304,98812305818937,98812685466930)]
theorem point_links_checked18222 : (cuts18222.take 2).map (fun c => (2392326145-1+2*2^9*c.k,98811808726060+c.lower,98812188373745+c.upper)) = pointBounds18222 := by
 decide +kernel
def cuts18223 : List PrefixCut := [⟨36,200828642,200828761⟩,
⟨110,611300002,611300370⟩,
⟨128,711062940,711063370⟩]
theorem checked18223 : checkPrefixCuts (2^48) 2392457217 9 Manual.Count131072.C018223.packed 128 cuts18223 = true := by
 decide +kernel
def pointBounds18223 : List (Nat × Nat × Nat) := [(2392494080,98812720538762,98813100187005),(2392569856,98813131010122,98813510658614)]
theorem point_links_checked18223 : (cuts18223.take 2).map (fun c => (2392457217-1+2*2^9*c.k,98812519710120+c.lower,98812899358244+c.upper)) = pointBounds18223 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000256
