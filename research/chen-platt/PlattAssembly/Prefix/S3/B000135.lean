import PlattAssemblyKernel
import PlattCertificates.Count131072.C024320
import PlattCertificates.Count131072.C024321
import PlattCertificates.Count131072.C024322
import PlattCertificates.Count131072.C024323
import PlattCertificates.Count131072.C024324
import PlattCertificates.Count131072.C024325
import PlattCertificates.Count131072.C024326
import PlattCertificates.Count131072.C024327
import PlattCertificates.Count131072.C024328
import PlattCertificates.Count131072.C024329
import PlattCertificates.Count131072.C024330
import PlattCertificates.Count131072.C024331
import PlattCertificates.Count131072.C024332
import PlattCertificates.Count131072.C024333
import PlattCertificates.Count131072.C024334
import PlattCertificates.Count131072.C024335
import PlattCertificates.Count131072.C024336
import PlattCertificates.Count131072.C024337
import PlattCertificates.Count131072.C024338
import PlattCertificates.Count131072.C024339
import PlattCertificates.Count131072.C024340
import PlattCertificates.Count131072.C024341
import PlattCertificates.Count131072.C024342
import PlattCertificates.Count131072.C024343
import PlattCertificates.Count131072.C024344
import PlattCertificates.Count131072.C024345
import PlattCertificates.Count131072.C024346
import PlattCertificates.Count131072.C024347
import PlattCertificates.Count131072.C024348
import PlattCertificates.Count131072.C024349
import PlattCertificates.Count131072.C024350
import PlattCertificates.Count131072.C024351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000135
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24320 : List PrefixCut := [⟨78,325601973,325602152⟩,
⟨128,531524237,531524534⟩]
theorem checked24320 : checkPrefixCuts (2^48) 3191603201 9 Manual.Count131072.C024320.packed 128 cuts24320 = true := by
 decide +kernel
def pointBounds24320 : List (Nat × Nat × Nat) := [(3191683072,102544342052637,102544723870034)]
theorem point_links_checked24320 : (cuts24320.take 1).map (fun c => (3191603201-1+2*2^9*c.k,102544016450664+c.lower,102544398267882+c.upper)) = pointBounds24320 := by
 decide +kernel
def cuts24321 : List PrefixCut := [⟨48,200627744,200627854⟩,
⟨128,531590579,531590879⟩]
theorem checked24321 : checkPrefixCuts (2^48) 3191734273 9 Manual.Count131072.C024321.packed 128 cuts24321 = true := by
 decide +kernel
def pointBounds24321 : List (Nat × Nat × Nat) := [(3191783424,102544748602645,102545130420270)]
theorem point_links_checked24321 : (cuts24321.take 1).map (fun c => (3191734273-1+2*2^9*c.k,102544547974901+c.lower,102544929792416+c.upper)) = pointBounds24321 := by
 decide +kernel
def cuts24322 : List PrefixCut := [⟨18,73546150,73546194⟩,
⟨116,476367028,476367300⟩,
⟨128,527424193,527424493⟩]
theorem checked24322 : checkPrefixCuts (2^48) 3191865345 9 Manual.Count131072.C024322.packed 128 cuts24322 = true := by
 decide +kernel
def pointBounds24322 : List (Nat × Nat × Nat) := [(3191883776,102545153111630,102545534929489),(3191984128,102545555932508,102545937750595)]
theorem point_links_checked24322 : (cuts24322.take 2).map (fun c => (3191865345-1+2*2^9*c.k,102545079565480+c.lower,102545461383295+c.upper)) = pointBounds24322 := by
 decide +kernel
def cuts24323 : List PrefixCut := [⟨86,352809151,352809354⟩,
⟨128,525021639,525021935⟩]
theorem checked24323 : checkPrefixCuts (2^48) 3191996417 9 Manual.Count131072.C024323.packed 128 cuts24323 = true := by
 decide +kernel
def pointBounds24323 : List (Nat × Nat × Nat) := [(3192084480,102545959798824,102546341617142)]
theorem point_links_checked24323 : (cuts24323.take 1).map (fun c => (3191996417-1+2*2^9*c.k,102545606989673+c.lower,102545988807788+c.upper)) = pointBounds24323 := by
 decide +kernel
def cuts24324 : List PrefixCut := [⟨56,231464756,231464887⟩,
⟨128,525352780,525353079⟩]
theorem checked24324 : checkPrefixCuts (2^48) 3192127489 9 Manual.Count131072.C024324.packed 128 cuts24324 = true := by
 decide +kernel
def pointBounds24324 : List (Nat × Nat × Nat) := [(3192184832,102546363476068,102546745294610)]
theorem point_links_checked24324 : (cuts24324.take 1).map (fun c => (3192127489-1+2*2^9*c.k,102546132011312+c.lower,102546513829723+c.upper)) = pointBounds24324 := by
 decide +kernel
def cuts24325 : List PrefixCut := [⟨26,110305490,110305549⟩,
⟨124,516690692,516690979⟩,
⟨128,533707629,533707925⟩]
theorem checked24325 : checkPrefixCuts (2^48) 3192258561 9 Manual.Count131072.C024325.packed 128 cuts24325 = true := by
 decide +kernel
def pointBounds24325 : List (Nat × Nat × Nat) := [(3192285184,102546767669582,102547149488351),(3192385536,102547174054784,102547555873781)]
theorem point_links_checked24325 : (cuts24325.take 2).map (fun c => (3192258561-1+2*2^9*c.k,102546657364092+c.lower,102547039182802+c.upper)) = pointBounds24325 := by
 decide +kernel
def cuts24326 : List PrefixCut := [⟨94,386093192,386093412⟩,
⟨128,520724895,520725191⟩]
theorem checked24326 : checkPrefixCuts (2^48) 3192389633 9 Manual.Count131072.C024326.packed 128 cuts24326 = true := by
 decide +kernel
def pointBounds24326 : List (Nat × Nat × Nat) := [(3192485888,102547577164913,102547958984139)]
theorem point_links_checked24326 : (cuts24326.take 1).map (fun c => (3192389633-1+2*2^9*c.k,102547191071721+c.lower,102547572890727+c.upper)) = pointBounds24326 := by
 decide +kernel
def cuts24327 : List PrefixCut := [⟨64,259031891,259032029⟩,
⟨128,523436506,523436804⟩]
theorem checked24327 : checkPrefixCuts (2^48) 3192520705 9 Manual.Count131072.C024327.packed 128 cuts24327 = true := by
 decide +kernel
def pointBounds24327 : List (Nat × Nat × Nat) := [(3192586240,102547970828507,102548352647947)]
theorem point_links_checked24327 : (cuts24327.take 1).map (fun c => (3192520705-1+2*2^9*c.k,102547711796616+c.lower,102548093615918+c.upper)) = pointBounds24327 := by
 decide +kernel
def cuts24328 : List PrefixCut := [⟨34,140090831,140090906⟩,
⟨128,525002040,525002328⟩]
theorem checked24328 : checkPrefixCuts (2^48) 3192651777 9 Manual.Count131072.C024328.packed 128 cuts24328 = true := by
 decide +kernel
def pointBounds24328 : List (Nat × Nat × Nat) := [(3192686592,102548375323953,102548757143628)]
theorem point_links_checked24328 : (cuts24328.take 1).map (fun c => (3192651777-1+2*2^9*c.k,102548235233122+c.lower,102548617052722+c.upper)) = pointBounds24328 := by
 decide +kernel
def cuts24329 : List PrefixCut := [⟨4,15868743,15868751⟩,
⟨102,425804552,425804788⟩,
⟨128,533267316,533267614⟩]
theorem checked24329 : checkPrefixCuts (2^48) 3192782849 9 Manual.Count131072.C024329.packed 128 cuts24329 = true := by
 decide +kernel
def pointBounds24329 : List (Nat × Nat × Nat) := [(3192786944,102548776103905,102549157923801),(3192887296,102549186039714,102549567859838)]
theorem point_links_checked24329 : (cuts24329.take 2).map (fun c => (3192782849-1+2*2^9*c.k,102548760235162+c.lower,102549142055050+c.upper)) = pointBounds24329 := by
 decide +kernel
def cuts24330 : List PrefixCut := [⟨72,293027529,293027691⟩,
⟨128,523548378,523548677⟩]
theorem checked24330 : checkPrefixCuts (2^48) 3192913921 9 Manual.Count131072.C024330.packed 128 cuts24330 = true := by
 decide +kernel
def pointBounds24330 : List (Nat × Nat × Nat) := [(3192987648,102549586530007,102549968350355)]
theorem point_links_checked24330 : (cuts24330.take 1).map (fun c => (3192913921-1+2*2^9*c.k,102549293502478+c.lower,102549675322664+c.upper)) = pointBounds24330 := by
 decide +kernel
def cuts24331 : List PrefixCut := [⟨42,172336998,172337093⟩,
⟨128,529961934,529962233⟩]
theorem checked24331 : checkPrefixCuts (2^48) 3193044993 9 Manual.Count131072.C024331.packed 128 cuts24331 = true := by
 decide +kernel
def pointBounds24331 : List (Nat × Nat × Nat) := [(3193088000,102549989387854,102550371208434)]
theorem point_links_checked24331 : (cuts24331.take 1).map (fun c => (3193044993-1+2*2^9*c.k,102549817050856+c.lower,102550198871341+c.upper)) = pointBounds24331 := by
 decide +kernel
def cuts24332 : List PrefixCut := [⟨12,48746240,48746268⟩,
⟨110,452019430,452019683⟩,
⟨128,527119404,527119701⟩]
theorem checked24332 : checkPrefixCuts (2^48) 3193176065 9 Manual.Count131072.C024332.packed 128 cuts24332 = true := by
 decide +kernel
def pointBounds24332 : List (Nat × Nat × Nat) := [(3193188352,102550395759030,102550777579842),(3193288704,102550799032220,102551180853257)]
theorem point_links_checked24332 : (cuts24332.take 2).map (fun c => (3193176065-1+2*2^9*c.k,102550347012790+c.lower,102550728833574+c.upper)) = pointBounds24332 := by
 decide +kernel
def cuts24333 : List PrefixCut := [⟨80,328513150,328513334⟩,
⟨128,527362234,527362533⟩]
theorem checked24333 : checkPrefixCuts (2^48) 3193307137 9 Manual.Count131072.C024333.packed 128 cuts24333 = true := by
 decide +kernel
def pointBounds24333 : List (Nat × Nat × Nat) := [(3193389056,102551202645344,102551584466609)]
theorem point_links_checked24333 : (cuts24333.take 1).map (fun c => (3193307137-1+2*2^9*c.k,102550874132194+c.lower,102551255953275+c.upper)) = pointBounds24333 := by
 decide +kernel
def cuts24334 : List PrefixCut := [⟨50,207748179,207748292⟩,
⟨128,531130626,531130924⟩]
theorem checked24334 : checkPrefixCuts (2^48) 3193438209 9 Manual.Count131072.C024334.packed 128 cuts24334 = true := by
 decide +kernel
def pointBounds24334 : List (Nat × Nat × Nat) := [(3193489408,102551609242607,102551991064100)]
theorem point_links_checked24334 : (cuts24334.take 1).map (fun c => (3193438209-1+2*2^9*c.k,102551401494428+c.lower,102551783315808+c.upper)) = pointBounds24334 := by
 decide +kernel
def cuts24335 : List PrefixCut := [⟨20,79147699,79147743⟩,
⟨118,485807558,485807828⟩,
⟨128,526085047,526085342⟩]
theorem checked24335 : checkPrefixCuts (2^48) 3193569281 9 Manual.Count131072.C024335.packed 128 cuts24335 = true := by
 decide +kernel
def pointBounds24335 : List (Nat × Nat × Nat) := [(3193589760,102552011772753,102552393594475),(3193690112,102552418432612,102552800254560)]
theorem point_links_checked24335 : (cuts24335.take 2).map (fun c => (3193569281-1+2*2^9*c.k,102551932625054+c.lower,102552314446732+c.upper)) = pointBounds24335 := by
 decide +kernel
def cuts24336 : List PrefixCut := [⟨88,359671499,359671703⟩,
⟨128,523155182,523155476⟩]
theorem checked24336 : checkPrefixCuts (2^48) 3193700353 9 Manual.Count131072.C024336.packed 128 cuts24336 = true := by
 decide +kernel
def pointBounds24336 : List (Nat × Nat × Nat) := [(3193790464,102552818381600,102553200203777)]
theorem point_links_checked24336 : (cuts24336.take 1).map (fun c => (3193700353-1+2*2^9*c.k,102552458710101+c.lower,102552840532074+c.upper)) = pointBounds24336 := by
 decide +kernel
def cuts24337 : List PrefixCut := [⟨58,233544447,233544585⟩,
⟨128,523486083,523486386⟩]
theorem checked24337 : checkPrefixCuts (2^48) 3193831425 9 Manual.Count131072.C024337.packed 128 cuts24337 = true := by
 decide +kernel
def pointBounds24337 : List (Nat × Nat × Nat) := [(3193890816,102553215409730,102553597232135)]
theorem point_links_checked24337 : (cuts24337.take 1).map (fun c => (3193831425-1+2*2^9*c.k,102552981865283+c.lower,102553363687550+c.upper)) = pointBounds24337 := by
 decide +kernel
def cuts24338 : List PrefixCut := [⟨28,119676176,119676243⟩,
⟨126,519411147,519411437⟩,
⟨128,527694764,527695059⟩]
theorem checked24338 : checkPrefixCuts (2^48) 3193962497 9 Manual.Count131072.C024338.packed 128 cuts24338 = true := by
 decide +kernel
def pointBounds24338 : List (Nat × Nat × Nat) := [(3193991168,102553625027542,102554006850179),(3194091520,102554024762513,102554406585373)]
theorem point_links_checked24338 : (cuts24338.take 2).map (fun c => (3193962497-1+2*2^9*c.k,102553505351366+c.lower,102553887173936+c.upper)) = pointBounds24338 := by
 decide +kernel
def cuts24339 : List PrefixCut := [⟨96,394523120,394523342⟩,
⟨128,528025522,528025821⟩]
theorem checked24339 : checkPrefixCuts (2^48) 3194093569 9 Manual.Count131072.C024339.packed 128 cuts24339 = true := by
 decide +kernel
def pointBounds24339 : List (Nat × Nat × Nat) := [(3194191872,102554427569250,102554809392337)]
theorem point_links_checked24339 : (cuts24339.take 1).map (fun c => (3194093569-1+2*2^9*c.k,102554033046130+c.lower,102554414868995+c.upper)) = pointBounds24339 := by
 decide +kernel
def cuts24340 : List PrefixCut := [⟨66,267793687,267793838⟩,
⟨128,526241427,526241727⟩]
theorem checked24340 : checkPrefixCuts (2^48) 3194224641 9 Manual.Count131072.C024340.packed 128 cuts24340 = true := by
 decide +kernel
def pointBounds24340 : List (Nat × Nat × Nat) := [(3194292224,102554828865339,102555210688654)]
theorem point_links_checked24340 : (cuts24340.take 1).map (fun c => (3194224641-1+2*2^9*c.k,102554561071652+c.lower,102554942894816+c.upper)) = pointBounds24340 := by
 decide +kernel
def cuts24341 : List PrefixCut := [⟨36,151030502,151030593⟩,
⟨128,527806054,527806363⟩]
theorem checked24341 : checkPrefixCuts (2^48) 3194355713 9 Manual.Count131072.C024341.packed 128 cuts24341 = true := by
 decide +kernel
def pointBounds24341 : List (Nat × Nat × Nat) := [(3194392576,102555238343581,102555620167136)]
theorem point_links_checked24341 : (cuts24341.take 1).map (fun c => (3194355713-1+2*2^9*c.k,102555087313079+c.lower,102555469136543+c.upper)) = pointBounds24341 := by
 decide +kernel
def cuts24342 : List PrefixCut := [⟨6,24054746,24054761⟩,
⟨104,424431863,424432108⟩,
⟨128,521969005,521969305⟩]
theorem checked24342 : checkPrefixCuts (2^48) 3194486785 9 Manual.Count131072.C024342.packed 128 cuts24342 = true := by
 decide +kernel
def pointBounds24342 : List (Nat × Nat × Nat) := [(3194492928,102555639173879,102556020997667),(3194593280,102556039550996,102556421375014)]
theorem point_links_checked24342 : (cuts24342.take 2).map (fun c => (3194486785-1+2*2^9*c.k,102555615119133+c.lower,102555996942906+c.upper)) = pointBounds24342 := by
 decide +kernel
def cuts24343 : List PrefixCut := [⟨74,308378177,308378353⟩,
⟨128,536749555,536749857⟩]
theorem checked24343 : checkPrefixCuts (2^48) 3194617857 9 Manual.Count131072.C024343.packed 128 cuts24343 = true := by
 decide +kernel
def pointBounds24343 : List (Nat × Nat × Nat) := [(3194693632,102556445466315,102556827290564)]
theorem point_links_checked24343 : (cuts24343.take 1).map (fun c => (3194617857-1+2*2^9*c.k,102556137088138+c.lower,102556518912211+c.upper)) = pointBounds24343 := by
 decide +kernel
def cuts24344 : List PrefixCut := [⟨44,179293406,179293512⟩,
⟨128,525186037,525186335⟩]
theorem checked24344 : checkPrefixCuts (2^48) 3194748929 9 Manual.Count131072.C024344.packed 128 cuts24344 = true := by
 decide +kernel
def pointBounds24344 : List (Nat × Nat × Nat) := [(3194793984,102556853131099,102557234955580)]
theorem point_links_checked24344 : (cuts24344.take 1).map (fun c => (3194748929-1+2*2^9*c.k,102556673837693+c.lower,102557055662068+c.upper)) = pointBounds24344 := by
 decide +kernel
def cuts24345 : List PrefixCut := [⟨14,58587613,58587646⟩,
⟨112,459178710,459178971⟩,
⟨128,526397849,526398148⟩]
theorem checked24345 : checkPrefixCuts (2^48) 3194880001 9 Manual.Count131072.C024345.packed 128 cuts24345 = true := by
 decide +kernel
def pointBounds24345 : List (Nat × Nat × Nat) := [(3194894336,102557257611343,102557639436049),(3194994688,102557658202440,102558040027374)]
theorem point_links_checked24345 : (cuts24345.take 2).map (fun c => (3194880001-1+2*2^9*c.k,102557199023730+c.lower,102557580848403+c.upper)) = pointBounds24345 := by
 decide +kernel
def cuts24346 : List PrefixCut := [⟨82,341552480,341552670⟩,
⟨128,529988279,529988579⟩]
theorem checked24346 : checkPrefixCuts (2^48) 3195011073 9 Manual.Count131072.C024346.packed 128 cuts24346 = true := by
 decide +kernel
def pointBounds24346 : List (Nat × Nat × Nat) := [(3195095040,102558066974059,102558448799221)]
theorem point_links_checked24346 : (cuts24346.take 1).map (fun c => (3195011073-1+2*2^9*c.k,102557725421579+c.lower,102558107246551+c.upper)) = pointBounds24346 := by
 decide +kernel
def cuts24347 : List PrefixCut := [⟨52,220851437,220851563⟩,
⟨128,530230902,530231203⟩]
theorem checked24347 : checkPrefixCuts (2^48) 3195142145 9 Manual.Count131072.C024347.packed 128 cuts24347 = true := by
 decide +kernel
def pointBounds24347 : List (Nat × Nat × Nat) := [(3195195392,102558476261295,102558858086693)]
theorem point_links_checked24347 : (cuts24347.take 1).map (fun c => (3195142145-1+2*2^9*c.k,102558255409858+c.lower,102558637235130+c.upper)) = pointBounds24347 := by
 decide +kernel
def cuts24348 : List PrefixCut := [⟨22,92759524,92759577⟩,
⟨120,496119185,496119467⟩,
⟨128,530209057,530209359⟩]
theorem checked24348 : checkPrefixCuts (2^48) 3195273217 9 Manual.Count131072.C024348.packed 128 cuts24348 = true := by
 decide +kernel
def pointBounds24348 : List (Nat × Nat × Nat) := [(3195295744,102558878400284,102559260225910),(3195396096,102559281759945,102559663585800)]
theorem point_links_checked24348 : (cuts24348.take 2).map (fun c => (3195273217-1+2*2^9*c.k,102558785640760+c.lower,102559167466333+c.upper)) = pointBounds24348 := by
 decide +kernel
def cuts24349 : List PrefixCut := [⟨90,376568271,376568488⟩,
⟨128,531949021,531949328⟩]
theorem checked24349 : checkPrefixCuts (2^48) 3195404289 9 Manual.Count131072.C024349.packed 128 cuts24349 = true := by
 decide +kernel
def pointBounds24349 : List (Nat × Nat × Nat) := [(3195496448,102559692418088,102560074244180)]
theorem point_links_checked24349 : (cuts24349.take 1).map (fun c => (3195404289-1+2*2^9*c.k,102559315849817+c.lower,102559697675692+c.upper)) = pointBounds24349 := by
 decide +kernel
def cuts24350 : List PrefixCut := [⟨60,250507891,250508038⟩,
⟨128,527963506,527963809⟩]
theorem checked24350 : checkPrefixCuts (2^48) 3195535361 9 Manual.Count131072.C024350.packed 128 cuts24350 = true := by
 decide +kernel
def pointBounds24350 : List (Nat × Nat × Nat) := [(3195596800,102560098306729,102560480133058)]
theorem point_links_checked24350 : (cuts24350.take 1).map (fun c => (3195535361-1+2*2^9*c.k,102559847798838+c.lower,102560229625020+c.upper)) = pointBounds24350 := by
 decide +kernel
def cuts24351 : List PrefixCut := [⟨30,123399743,123399816⟩,
⟨128,523714001,523714305⟩]
theorem checked24351 : checkPrefixCuts (2^48) 3195666433 9 Manual.Count131072.C024351.packed 128 cuts24351 = true := by
 decide +kernel
def pointBounds24351 : List (Nat × Nat × Nat) := [(3195697152,102560499162087,102560880988645),(3195797504,102560899476345,102561281303134)]
theorem point_links_checked24351 : (cuts24351.take 2).map (fun c => (3195666433-1+2*2^9*c.k,102560375762344+c.lower,102560757588829+c.upper)) = pointBounds24351 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000135
