import PlattAssemblyKernel
import PlattCertificates.Count131072.C022432
import PlattCertificates.Count131072.C022433
import PlattCertificates.Count131072.C022434
import PlattCertificates.Count131072.C022435
import PlattCertificates.Count131072.C022436
import PlattCertificates.Count131072.C022437
import PlattCertificates.Count131072.C022438
import PlattCertificates.Count131072.C022439
import PlattCertificates.Count131072.C022440
import PlattCertificates.Count131072.C022441
import PlattCertificates.Count131072.C022442
import PlattCertificates.Count131072.C022443
import PlattCertificates.Count131072.C022444
import PlattCertificates.Count131072.C022445
import PlattCertificates.Count131072.C022446
import PlattCertificates.Count131072.C022447
import PlattCertificates.Count131072.C022448
import PlattCertificates.Count131072.C022449
import PlattCertificates.Count131072.C022450
import PlattCertificates.Count131072.C022451
import PlattCertificates.Count131072.C022452
import PlattCertificates.Count131072.C022453
import PlattCertificates.Count131072.C022454
import PlattCertificates.Count131072.C022455
import PlattCertificates.Count131072.C022456
import PlattCertificates.Count131072.C022457
import PlattCertificates.Count131072.C022458
import PlattCertificates.Count131072.C022459
import PlattCertificates.Count131072.C022460
import PlattCertificates.Count131072.C022461
import PlattCertificates.Count131072.C022462
import PlattCertificates.Count131072.C022463
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000076
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22432 : List PrefixCut := [⟨52,232796450,232796578⟩,
⟨128,571801746,571802066⟩]
theorem checked22432 : checkPrefixCuts (2^48) 2944139265 9 Manual.Count131072.C022432.packed 128 cuts22432 = true := by
 decide +kernel
def pointBounds22432 : List (Nat × Nat × Nat) := [(2944192512,101504343591478,101504724819470)]
theorem point_links_checked22432 : (cuts22432.take 1).map (fun c => (2944139265-1+2*2^9*c.k,101504110795028+c.lower,101504492022892+c.upper)) = pointBounds22432 := by
 decide +kernel
def cuts22433 : List PrefixCut := [⟨14,65390854,65390890⟩,
⟨104,469200770,469201040⟩,
⟨128,578850572,578850906⟩]
theorem checked22433 : checkPrefixCuts (2^48) 2944270337 9 Manual.Count131072.C022433.packed 128 cuts22433 = true := by
 decide +kernel
def pointBounds22433 : List (Nat × Nat × Nat) := [(2944284672,101504747987628,101505129215848),(2944376832,101505151797544,101505533025998)]
theorem point_links_checked22433 : (cuts22433.take 2).map (fun c => (2944270337-1+2*2^9*c.k,101504682596774+c.lower,101505063824958+c.upper)) = pointBounds22433 := by
 decide +kernel
def cuts22434 : List PrefixCut := [⟨66,297875690,297875861⟩,
⟨128,575287815,575288144⟩]
theorem checked22434 : checkPrefixCuts (2^48) 2944401409 9 Manual.Count131072.C022434.packed 128 cuts22434 = true := by
 decide +kernel
def pointBounds22434 : List (Nat × Nat × Nat) := [(2944468992,101505559323036,101505940551725)]
theorem point_links_checked22434 : (cuts22434.take 1).map (fun c => (2944401409-1+2*2^9*c.k,101505261447346+c.lower,101505642675864+c.upper)) = pointBounds22434 := by
 decide +kernel
def cuts22435 : List PrefixCut := [⟨28,125607789,125607861⟩,
⟨118,530622503,530622813⟩,
⟨128,573446063,573446400⟩]
theorem checked22435 : checkPrefixCuts (2^48) 2944532481 9 Manual.Count131072.C022435.packed 128 cuts22435 = true := by
 decide +kernel
def pointBounds22435 : List (Nat × Nat × Nat) := [(2944561152,101505962342950,101506343571869),(2944653312,101506367357664,101506748586821)]
theorem point_links_checked22435 : (cuts22435.take 2).map (fun c => (2944532481-1+2*2^9*c.k,101505836735161+c.lower,101506217964008+c.upper)) = pointBounds22435 := by
 decide +kernel
def cuts22436 : List PrefixCut := [⟨80,357207925,357208123⟩,
⟨128,568258880,568259198⟩]
theorem checked22436 : checkPrefixCuts (2^48) 2944663553 9 Manual.Count131072.C022436.packed 128 cuts22436 = true := by
 decide +kernel
def pointBounds22436 : List (Nat × Nat × Nat) := [(2944745472,101506767389149,101507148618531)]
theorem point_links_checked22436 : (cuts22436.take 1).map (fun c => (2944663553-1+2*2^9*c.k,101506410181224+c.lower,101506791410408+c.upper)) = pointBounds22436 := by
 decide +kernel
def cuts22437 : List PrefixCut := [⟨42,186482820,186482924⟩,
⟨128,566321875,566322190⟩]
theorem checked22437 : checkPrefixCuts (2^48) 2944794625 9 Manual.Count131072.C022437.packed 128 cuts22437 = true := by
 decide +kernel
def pointBounds22437 : List (Nat × Nat × Nat) := [(2944837632,101507164922924,101507546152530)]
theorem point_links_checked22437 : (cuts22437.take 1).map (fun c => (2944794625-1+2*2^9*c.k,101506978440104+c.lower,101507359669606+c.upper)) = pointBounds22437 := by
 decide +kernel
def cuts22438 : List PrefixCut := [⟨4,17968957,17968968⟩,
⟨94,426086953,426087197⟩,
⟨128,578626128,578626463⟩]
theorem checked22438 : checkPrefixCuts (2^48) 2944925697 9 Manual.Count131072.C022438.packed 128 cuts22438 = true := by
 decide +kernel
def pointBounds22438 : List (Nat × Nat × Nat) := [(2944929792,101507562730936,101507943960764),(2945021952,101507970848932,101508352078993)]
theorem point_links_checked22438 : (cuts22438.take 2).map (fun c => (2944925697-1+2*2^9*c.k,101507544761979+c.lower,101507925991796+c.upper)) = pointBounds22438 := by
 decide +kernel
def cuts22439 : List PrefixCut := [⟨56,255757220,255757361⟩,
⟨128,581658820,581659152⟩]
theorem checked22439 : checkPrefixCuts (2^48) 2945056769 9 Manual.Count131072.C022439.packed 128 cuts22439 = true := by
 decide +kernel
def pointBounds22439 : List (Nat × Nat × Nat) := [(2945114112,101508379145327,101508760375620)]
theorem point_links_checked22439 : (cuts22439.take 1).map (fun c => (2945056769-1+2*2^9*c.k,101508123388107+c.lower,101508504618259+c.upper)) = pointBounds22439 := by
 decide +kernel
def cuts22440 : List PrefixCut := [⟨18,78750349,78750394⟩,
⟨108,477177638,477177915⟩,
⟨128,567679782,567680114⟩]
theorem checked22440 : checkPrefixCuts (2^48) 2945187841 9 Manual.Count131072.C022440.packed 128 cuts22440 = true := by
 decide +kernel
def pointBounds22440 : List (Nat × Nat × Nat) := [(2945206272,101508783797276,101509165027805),(2945298432,101509182224565,101509563455326)]
theorem point_links_checked22440 : (cuts22440.take 2).map (fun c => (2945187841-1+2*2^9*c.k,101508705046927+c.lower,101509086277411+c.upper)) = pointBounds22440 := by
 decide +kernel
def cuts22441 : List PrefixCut := [⟨70,309728436,309728621⟩,
⟨128,566985600,566985935⟩]
theorem checked22441 : checkPrefixCuts (2^48) 2945318913 9 Manual.Count131072.C022441.packed 128 cuts22441 = true := by
 decide +kernel
def pointBounds22441 : List (Nat × Nat × Nat) := [(2945390592,101509582455145,101509963686146)]
theorem point_links_checked22441 : (cuts22441.take 1).map (fun c => (2945318913-1+2*2^9*c.k,101509272726709+c.lower,101509653957525+c.upper)) = pointBounds22441 := by
 decide +kernel
def cuts22442 : List PrefixCut := [⟨32,145541044,145541128⟩,
⟨122,552149070,552149389⟩,
⟨128,577089827,577090160⟩]
theorem checked22442 : checkPrefixCuts (2^48) 2945449985 9 Manual.Count131072.C022442.packed 128 cuts22442 = true := by
 decide +kernel
def pointBounds22442 : List (Nat × Nat × Nat) := [(2945482752,101509985253353,101510366484588),(2945574912,101510391861379,101510773092849)]
theorem point_links_checked22442 : (cuts22442.take 2).map (fun c => (2945449985-1+2*2^9*c.k,101509839712309+c.lower,101510220943460+c.upper)) = pointBounds22442 := by
 decide +kernel
def cuts22443 : List PrefixCut := [⟨84,378119012,378119223⟩,
⟨128,579166399,579166722⟩]
theorem checked22443 : checkPrefixCuts (2^48) 2945581057 9 Manual.Count131072.C022443.packed 128 cuts22443 = true := by
 decide +kernel
def pointBounds22443 : List (Nat × Nat × Nat) := [(2945667072,101510794921148,101511176152843)]
theorem point_links_checked22443 : (cuts22443.take 1).map (fun c => (2945581057-1+2*2^9*c.k,101510416802136+c.lower,101510798033620+c.upper)) = pointBounds22443 := by
 decide +kernel
def cuts22444 : List PrefixCut := [⟨46,208784063,208784175⟩,
⟨128,573598673,573598996⟩]
theorem checked22444 : checkPrefixCuts (2^48) 2945712129 9 Manual.Count131072.C022444.packed 128 cuts22444 = true := by
 decide +kernel
def pointBounds22444 : List (Nat × Nat × Nat) := [(2945759232,101511204752598,101511585984517)]
theorem point_links_checked22444 : (cuts22444.take 1).map (fun c => (2945712129-1+2*2^9*c.k,101510995968535+c.lower,101511377200342+c.upper)) = pointBounds22444 := by
 decide +kernel
def cuts22445 : List PrefixCut := [⟨8,37646593,37646612⟩,
⟨98,433980103,433980346⟩,
⟨128,574241784,574242108⟩]
theorem checked22445 : checkPrefixCuts (2^48) 2945843201 9 Manual.Count131072.C022445.packed 128 cuts22445 = true := by
 decide +kernel
def pointBounds22445 : List (Nat × Nat × Nat) := [(2945851392,101511607213801,101511988445950),(2945943552,101512003547311,101512384779684)]
theorem point_links_checked22445 : (cuts22445.take 2).map (fun c => (2945843201-1+2*2^9*c.k,101511569567208+c.lower,101511950799338+c.upper)) = pointBounds22445 := by
 decide +kernel
def cuts22446 : List PrefixCut := [⟨60,276506112,276506268⟩,
⟨128,578706958,578707293⟩]
theorem checked22446 : checkPrefixCuts (2^48) 2945974273 9 Manual.Count131072.C022446.packed 128 cuts22446 = true := by
 decide +kernel
def pointBounds22446 : List (Nat × Nat × Nat) := [(2946035712,101512420315104,101512801547714)]
theorem point_links_checked22446 : (cuts22446.take 1).map (fun c => (2945974273-1+2*2^9*c.k,101512143808992+c.lower,101512525041446+c.upper)) = pointBounds22446 := by
 decide +kernel
def cuts22447 : List PrefixCut := [⟨22,96687482,96687540⟩,
⟨112,502919847,502920139⟩,
⟨128,572471052,572471384⟩]
theorem checked22447 : checkPrefixCuts (2^48) 2946105345 9 Manual.Count131072.C022447.packed 128 cuts22447 = true := by
 decide +kernel
def pointBounds22447 : List (Nat × Nat × Nat) := [(2946127872,101512819203432,101513200436279),(2946220032,101513225435797,101513606668878)]
theorem point_links_checked22447 : (cuts22447.take 2).map (fun c => (2946105345-1+2*2^9*c.k,101512722515950+c.lower,101513103748739+c.upper)) = pointBounds22447 := by
 decide +kernel
def cuts22448 : List PrefixCut := [⟨74,333802332,333802520⟩,
⟨128,575789325,575789645⟩]
theorem checked22448 : checkPrefixCuts (2^48) 2946236417 9 Manual.Count131072.C022448.packed 128 cuts22448 = true := by
 decide +kernel
def pointBounds22448 : List (Nat × Nat × Nat) := [(2946312192,101513628789334,101514010022643)]
theorem point_links_checked22448 : (cuts22448.take 1).map (fun c => (2946236417-1+2*2^9*c.k,101513294987002+c.lower,101513676220123+c.upper)) = pointBounds22448 := by
 decide +kernel
def cuts22449 : List PrefixCut := [⟨36,159920987,159921081⟩,
⟨126,563535941,563536269⟩,
⟨128,572324576,572324908⟩]
theorem checked22449 : checkPrefixCuts (2^48) 2946367489 9 Manual.Count131072.C022449.packed 128 cuts22449 = true := by
 decide +kernel
def pointBounds22449 : List (Nat × Nat × Nat) := [(2946404352,101514030697314,101514411930849),(2946496512,101514434312268,101514815546037)]
theorem point_links_checked22449 : (cuts22449.take 2).map (fun c => (2946367489-1+2*2^9*c.k,101513870776327+c.lower,101514252009768+c.upper)) = pointBounds22449 := by
 decide +kernel
def cuts22450 : List PrefixCut := [⟨88,390323914,390324140⟩,
⟨128,562746587,562746910⟩]
theorem checked22450 : checkPrefixCuts (2^48) 2946498561 9 Manual.Count131072.C022450.packed 128 cuts22450 = true := by
 decide +kernel
def pointBounds22450 : List (Nat × Nat × Nat) := [(2946588672,101514833424817,101515214658816)]
theorem point_links_checked22450 : (cuts22450.take 1).map (fun c => (2946498561-1+2*2^9*c.k,101514443100903+c.lower,101514824334676+c.upper)) = pointBounds22450 := by
 decide +kernel
def cuts22451 : List PrefixCut := [⟨50,225244498,225244628⟩,
⟨128,582016883,582017218⟩]
theorem checked22451 : checkPrefixCuts (2^48) 2946629633 9 Manual.Count131072.C022451.packed 128 cuts22451 = true := by
 decide +kernel
def pointBounds22451 : List (Nat × Nat × Nat) := [(2946680832,101515231091988,101515612326214)]
theorem point_links_checked22451 : (cuts22451.take 1).map (fun c => (2946629633-1+2*2^9*c.k,101515005847490+c.lower,101515387081586+c.upper)) = pointBounds22451 := by
 decide +kernel
def cuts22452 : List PrefixCut := [⟨12,53968750,53968780⟩,
⟨102,456100445,456100707⟩,
⟨128,572725824,572726152⟩]
theorem checked22452 : checkPrefixCuts (2^48) 2946760705 9 Manual.Count131072.C022452.packed 128 cuts22452 = true := by
 decide +kernel
def pointBounds22452 : List (Nat × Nat × Nat) := [(2946772992,101515641833123,101516023067584),(2946865152,101516043964818,101516425199511)]
theorem point_links_checked22452 : (cuts22452.take 2).map (fun c => (2946760705-1+2*2^9*c.k,101515587864373+c.lower,101515969098804+c.upper)) = pointBounds22452 := by
 decide +kernel
def cuts22453 : List PrefixCut := [⟨64,287786078,287786238⟩,
⟨128,573273463,573273784⟩]
theorem checked22453 : checkPrefixCuts (2^48) 2946891777 9 Manual.Count131072.C022453.packed 128 cuts22453 = true := by
 decide +kernel
def pointBounds22453 : List (Nat × Nat × Nat) := [(2946957312,101516448376275,101516829611194)]
theorem point_links_checked22453 : (cuts22453.take 1).map (fun c => (2946891777-1+2*2^9*c.k,101516160590197+c.lower,101516541824956+c.upper)) = pointBounds22453 := by
 decide +kernel
def cuts22454 : List PrefixCut := [⟨26,118815907,118815977⟩,
⟨116,524061628,524061930⟩,
⟨128,574871651,574871984⟩]
theorem checked22454 : checkPrefixCuts (2^48) 2947022849 9 Manual.Count131072.C022454.packed 128 cuts22454 = true := by
 decide +kernel
def pointBounds22454 : List (Nat × Nat × Nat) := [(2947049472,101516852679567,101517233914717),(2947141632,101517257925288,101517639160670)]
theorem point_links_checked22454 : (cuts22454.take 2).map (fun c => (2947022849-1+2*2^9*c.k,101516733863660+c.lower,101517115098740+c.upper)) = pointBounds22454 := by
 decide +kernel
def cuts22455 : List PrefixCut := [⟨78,354422966,354423171⟩,
⟨128,579812272,579812612⟩]
theorem checked22455 : checkPrefixCuts (2^48) 2947153921 9 Manual.Count131072.C022455.packed 128 cuts22455 = true := by
 decide +kernel
def pointBounds22455 : List (Nat × Nat × Nat) := [(2947233792,101517663158277,101518044393895)]
theorem point_links_checked22455 : (cuts22455.take 1).map (fun c => (2947153921-1+2*2^9*c.k,101517308735311+c.lower,101517689970724+c.upper)) = pointBounds22455 := by
 decide +kernel
def cuts22456 : List PrefixCut := [⟨40,181359172,181359274⟩,
⟨128,574438583,574438910⟩]
theorem checked22456 : checkPrefixCuts (2^48) 2947284993 9 Manual.Count131072.C022456.packed 128 cuts22456 = true := by
 decide +kernel
def pointBounds22456 : List (Nat × Nat × Nat) := [(2947325952,101518069906755,101518451142610)]
theorem point_links_checked22456 : (cuts22456.take 1).map (fun c => (2947284993-1+2*2^9*c.k,101517888547583+c.lower,101518269783336+c.upper)) = pointBounds22456 := by
 decide +kernel
def cuts22457 : List PrefixCut := [⟨2,8499396,8499401⟩,
⟨92,413503467,413503704⟩,
⟨128,579092180,579092512⟩]
theorem checked22457 : checkPrefixCuts (2^48) 2947416065 9 Manual.Count131072.C022457.packed 128 cuts22457 = true := by
 decide +kernel
def pointBounds22457 : List (Nat × Nat × Nat) := [(2947418112,101518471485562,101518852721647),(2947510272,101518876489633,101519257725950)]
theorem point_links_checked22457 : (cuts22457.take 2).map (fun c => (2947416065-1+2*2^9*c.k,101518462986166+c.lower,101518844222246+c.upper)) = pointBounds22457 := by
 decide +kernel
def cuts22458 : List PrefixCut := [⟨54,242076599,242076741⟩,
⟨128,574291885,574292219⟩]
theorem checked22458 : checkPrefixCuts (2^48) 2947547137 9 Manual.Count131072.C022458.packed 128 cuts22458 = true := by
 decide +kernel
def pointBounds22458 : List (Nat × Nat × Nat) := [(2947602432,101519284154945,101519665391499)]
theorem point_links_checked22458 : (cuts22458.take 1).map (fun c => (2947547137-1+2*2^9*c.k,101519042078346+c.lower,101519423314758+c.upper)) = pointBounds22458 := by
 decide +kernel
def cuts22459 : List PrefixCut := [⟨16,73049932,73049972⟩,
⟨106,480976105,480976368⟩,
⟨128,579136224,579136546⟩]
theorem checked22459 : checkPrefixCuts (2^48) 2947678209 9 Manual.Count131072.C022459.packed 128 cuts22459 = true := by
 decide +kernel
def pointBounds22459 : List (Nat × Nat × Nat) := [(2947694592,101519689420163,101520070656949),(2947786752,101520097346336,101520478583345)]
theorem point_links_checked22459 : (cuts22459.take 2).map (fun c => (2947678209-1+2*2^9*c.k,101519616370231+c.lower,101519997606977+c.upper)) = pointBounds22459 := by
 decide +kernel
def cuts22460 : List PrefixCut := [⟨68,300968720,300968889⟩,
⟨128,571853633,571853953⟩]
theorem checked22460 : checkPrefixCuts (2^48) 2947809281 9 Manual.Count131072.C022460.packed 128 cuts22460 = true := by
 decide +kernel
def pointBounds22460 : List (Nat × Nat × Nat) := [(2947878912,101520496475175,101520877712412)]
theorem point_links_checked22460 : (cuts22460.take 1).map (fun c => (2947809281-1+2*2^9*c.k,101520195506455+c.lower,101520576743523+c.upper)) = pointBounds22460 := by
 decide +kernel
def cuts22461 : List PrefixCut := [⟨30,131286898,131286975⟩,
⟨120,534687303,534687612⟩,
⟨128,569727643,569727973⟩]
theorem checked22461 : checkPrefixCuts (2^48) 2947940353 9 Manual.Count131072.C022461.packed 128 cuts22461 = true := by
 decide +kernel
def pointBounds22461 : List (Nat × Nat × Nat) := [(2947971072,101520898646986,101521279884451),(2948063232,101521302047391,101521683285088)]
theorem point_links_checked22461 : (cuts22461.take 2).map (fun c => (2947940353-1+2*2^9*c.k,101520767360088+c.lower,101521148597476+c.upper)) = pointBounds22461 := by
 decide +kernel
def cuts22462 : List PrefixCut := [⟨82,368347483,368347701⟩,
⟨128,571230038,571230374⟩]
theorem checked22462 : checkPrefixCuts (2^48) 2948071425 9 Manual.Count131072.C022462.packed 128 cuts22462 = true := by
 decide +kernel
def pointBounds22462 : List (Nat × Nat × Nat) := [(2948155392,101521705435214,101522086673150)]
theorem point_links_checked22462 : (cuts22462.take 1).map (fun c => (2948071425-1+2*2^9*c.k,101521337087731+c.lower,101521718325449+c.upper)) = pointBounds22462 := by
 decide +kernel
def cuts22463 : List PrefixCut := [⟨44,196196323,196196437⟩,
⟨128,574546151,574546480⟩]
theorem checked22463 : checkPrefixCuts (2^48) 2948202497 9 Manual.Count131072.C022463.packed 128 cuts22463 = true := by
 decide +kernel
def pointBounds22463 : List (Nat × Nat × Nat) := [(2948247552,101522104514092,101522485752260)]
theorem point_links_checked22463 : (cuts22463.take 1).map (fun c => (2948202497-1+2*2^9*c.k,101521908317769+c.lower,101522289555823+c.upper)) = pointBounds22463 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000076
