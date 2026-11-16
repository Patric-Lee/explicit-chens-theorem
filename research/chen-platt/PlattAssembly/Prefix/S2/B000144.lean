import PlattAssemblyKernel
import PlattCertificates.Count131072.C014608
import PlattCertificates.Count131072.C014609
import PlattCertificates.Count131072.C014610
import PlattCertificates.Count131072.C014611
import PlattCertificates.Count131072.C014612
import PlattCertificates.Count131072.C014613
import PlattCertificates.Count131072.C014614
import PlattCertificates.Count131072.C014615
import PlattCertificates.Count131072.C014616
import PlattCertificates.Count131072.C014617
import PlattCertificates.Count131072.C014618
import PlattCertificates.Count131072.C014619
import PlattCertificates.Count131072.C014620
import PlattCertificates.Count131072.C014621
import PlattCertificates.Count131072.C014622
import PlattCertificates.Count131072.C014623
import PlattCertificates.Count131072.C014624
import PlattCertificates.Count131072.C014625
import PlattCertificates.Count131072.C014626
import PlattCertificates.Count131072.C014627
import PlattCertificates.Count131072.C014628
import PlattCertificates.Count131072.C014629
import PlattCertificates.Count131072.C014630
import PlattCertificates.Count131072.C014631
import PlattCertificates.Count131072.C014632
import PlattCertificates.Count131072.C014633
import PlattCertificates.Count131072.C014634
import PlattCertificates.Count131072.C014635
import PlattCertificates.Count131072.C014636
import PlattCertificates.Count131072.C014637
import PlattCertificates.Count131072.C014638
import PlattCertificates.Count131072.C014639
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000144
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14608 : List PrefixCut := [⟨37,264655049,264655233⟩,
⟨96,688473618,688474086⟩,
⟨128,907786012,907786630⟩]
theorem checked14608 : checkPrefixCuts (2^48) 1918631937 9 Manual.Count131072.C014608.packed 128 cuts14608 = true := by
 decide +kernel
def pointBounds14608 : List (Nat × Nat × Nat) := [(1918669824,95921219307834,95921597108660),(1918730240,95921643126403,95922020927513)]
theorem point_links_checked14608 : (cuts14608.take 2).map (fun c => (1918631937-1+2*2^9*c.k,95920954652785+c.lower,95921332453427+c.upper)) = pointBounds14608 := by
 decide +kernel
def cuts14609 : List PrefixCut := [⟨27,192610472,192610601⟩,
⟨86,616695840,616696258⟩,
⟨128,916085287,916085909⟩]
theorem checked14609 : checkPrefixCuts (2^48) 1918763009 9 Manual.Count131072.C014609.packed 128 cuts14609 = true := by
 decide +kernel
def pointBounds14609 : List (Nat × Nat × Nat) := [(1918790656,95922055049269,95922432850658),(1918851072,95922479134637,95922856936315)]
theorem point_links_checked14609 : (cuts14609.take 2).map (fun c => (1918763009-1+2*2^9*c.k,95921862438797+c.lower,95922240240057+c.upper)) = pointBounds14609 := by
 decide +kernel
def cuts14610 : List PrefixCut := [⟨17,120722031,120722110⟩,
⟨76,537446598,537446957⟩,
⟨128,891673956,891674553⟩]
theorem checked14610 : checkPrefixCuts (2^48) 1918894081 9 Manual.Count131072.C014610.packed 128 cuts14610 = true := by
 decide +kernel
def pointBounds14610 : List (Nat × Nat × Nat) := [(1918911488,95922899246115,95923277048076),(1918971904,95923315970682,95923693772923)]
theorem point_links_checked14610 : (cuts14610.take 2).map (fun c => (1918894081-1+2*2^9*c.k,95922778524084+c.lower,95923156325966+c.upper)) = pointBounds14610 := by
 decide +kernel
def cuts14611 : List PrefixCut := [⟨7,48256303,48256336⟩,
⟨66,463927936,463928249⟩,
⟨125,876799742,876800340⟩,
⟨128,897772992,897773604⟩]
theorem checked14611 : checkPrefixCuts (2^48) 1919025153 9 Manual.Count131072.C014611.packed 128 cuts14611 = true := by
 decide +kernel
def pointBounds14611 : List (Nat × Nat × Nat) := [(1919032320,95923718454343,95924096256855),(1919092736,95924134125976,95924511928768),(1919153152,95924546997782,95924924800859)]
theorem point_links_checked14611 : (cuts14611.take 3).map (fun c => (1919025153-1+2*2^9*c.k,95923670198040+c.lower,95924048000519+c.upper)) = pointBounds14611 := by
 decide +kernel
def cuts14612 : List PrefixCut := [⟨56,395845483,395845752⟩,
⟨115,820277433,820277991⟩,
⟨128,909004580,909005198⟩]
theorem checked14612 : checkPrefixCuts (2^48) 1919156225 9 Manual.Count131072.C014612.packed 128 cuts14612 = true := by
 decide +kernel
def pointBounds14612 : List (Nat × Nat × Nat) := [(1919213568,95924963816515,95925341619875),(1919273984,95925388248465,95925766052114)]
theorem point_links_checked14612 : (cuts14612.take 2).map (fun c => (1919156225-1+2*2^9*c.k,95924567971032+c.lower,95924945774123+c.upper)) = pointBounds14612 := by
 decide +kernel
def cuts14613 : List PrefixCut := [⟨46,316626266,316626479⟩,
⟨105,720647160,720647651⟩,
⟨128,881518743,881519342⟩]
theorem checked14613 : checkPrefixCuts (2^48) 1919287297 9 Manual.Count131072.C014613.packed 128 cuts14613 = true := by
 decide +kernel
def pointBounds14613 : List (Nat × Nat × Nat) := [(1919334400,95925793601878,95926171405800),(1919394816,95926197622772,95926575426972)]
theorem point_links_checked14613 : (cuts14613.take 2).map (fun c => (1919287297-1+2*2^9*c.k,95925476975612+c.lower,95925854779321+c.upper)) = pointBounds14613 := by
 decide +kernel
def cuts14614 : List PrefixCut := [⟨36,250468817,250468987⟩,
⟨95,665755578,665756032⟩,
⟨128,899935224,899935842⟩]
theorem checked14614 : checkPrefixCuts (2^48) 1919418369 9 Manual.Count131072.C014614.packed 128 cuts14614 = true := by
 decide +kernel
def pointBounds14614 : List (Nat × Nat × Nat) := [(1919455232,95926608963172,95926986767650),(1919515648,95927024249933,95927402054695)]
theorem point_links_checked14614 : (cuts14614.take 2).map (fun c => (1919418369-1+2*2^9*c.k,95926358494355+c.lower,95926736298663+c.upper)) = pointBounds14614 := by
 decide +kernel
def cuts14615 : List PrefixCut := [⟨26,185786428,185786553⟩,
⟨85,606765608,606766022⟩,
⟨128,914830163,914830781⟩]
theorem checked14615 : checkPrefixCuts (2^48) 1919549441 9 Manual.Count131072.C014615.packed 128 cuts14615 = true := by
 decide +kernel
def pointBounds14615 : List (Nat × Nat × Nat) := [(1919576064,95927444216007,95927822021058),(1919636480,95927865195187,95928243000527)]
theorem point_links_checked14615 : (cuts14615.take 2).map (fun c => (1919549441-1+2*2^9*c.k,95927258429579+c.lower,95927636234505+c.upper)) = pointBounds14615 := by
 decide +kernel
def cuts14616 : List PrefixCut := [⟨16,115247470,115247548⟩,
⟨75,525203518,525203878⟩,
⟨128,893654456,893655064⟩]
theorem checked14616 : checkPrefixCuts (2^48) 1919680513 9 Manual.Count131072.C014616.packed 128 cuts14616 = true := by
 decide +kernel
def pointBounds14616 : List (Nat × Nat × Nat) := [(1919696896,95928288507212,95928666312834),(1919757312,95928698463260,95929076269164)]
theorem point_links_checked14616 : (cuts14616.take 2).map (fun c => (1919680513-1+2*2^9*c.k,95928173259742+c.lower,95928551065286+c.upper)) = pointBounds14616 := by
 decide +kernel
def cuts14617 : List PrefixCut := [⟨6,41932076,41932105⟩,
⟨65,463444791,463445098⟩,
⟨124,873362191,873362776⟩,
⟨128,902536791,902537395⟩]
theorem checked14617 : checkPrefixCuts (2^48) 1919811585 9 Manual.Count131072.C014617.packed 128 cuts14617 = true := by
 decide +kernel
def pointBounds14617 : List (Nat × Nat × Nat) := [(1919817728,95929108846274,95929486652455),(1919878144,95929530358989,95929908165448),(1919938560,95929940276389,95930318083126)]
theorem point_links_checked14617 : (cuts14617.take 3).map (fun c => (1919811585-1+2*2^9*c.k,95929066914198+c.lower,95929444720350+c.upper)) = pointBounds14617 := by
 decide +kernel
def cuts14618 : List PrefixCut := [⟨55,388060096,388060354⟩,
⟨114,800004057,800004594⟩,
⟨128,900569198,900569803⟩]
theorem checked14618 : checkPrefixCuts (2^48) 1919942657 9 Manual.Count131072.C014618.packed 128 cuts14618 = true := by
 decide +kernel
def pointBounds14618 : List (Nat × Nat × Nat) := [(1919998976,95930357511085,95930735318099),(1920059392,95930769455046,95931147262339)]
theorem point_links_checked14618 : (cuts14618.take 2).map (fun c => (1919942657-1+2*2^9*c.k,95929969450989+c.lower,95930347257745+c.upper)) = pointBounds14618 := by
 decide +kernel
def cuts14619 : List PrefixCut := [⟨45,322653683,322653900⟩,
⟨104,739848895,739849394⟩,
⟨128,905345371,905345981⟩]
theorem checked14619 : checkPrefixCuts (2^48) 1920073729 9 Manual.Count131072.C014619.packed 128 cuts14619 = true := by
 decide +kernel
def pointBounds14619 : List (Nat × Nat × Nat) := [(1920119808,95931192673870,95931570481448),(1920180224,95931609869082,95931987676942)]
theorem point_links_checked14619 : (cuts14619.take 2).map (fun c => (1920073729-1+2*2^9*c.k,95930870020187+c.lower,95931247827548+c.upper)) = pointBounds14619 := by
 decide +kernel
def cuts14620 : List PrefixCut := [⟨35,251099234,251099407⟩,
⟨94,656981634,656982080⟩,
⟨128,893850365,893850972⟩]
theorem checked14620 : checkPrefixCuts (2^48) 1920204801 9 Manual.Count131072.C014620.packed 128 cuts14620 = true := by
 decide +kernel
def pointBounds14620 : List (Nat × Nat × Nat) := [(1920240640,95932026464792,95932404272936),(1920301056,95932432347192,95932810155609)]
theorem point_links_checked14620 : (cuts14620.take 2).map (fun c => (1920204801-1+2*2^9*c.k,95931775365558+c.lower,95932153173529+c.upper)) = pointBounds14620 := by
 decide +kernel
def cuts14621 : List PrefixCut := [⟨25,168854260,168854373⟩,
⟨84,577495891,577496281⟩,
⟨128,880011345,880011939⟩]
theorem checked14621 : checkPrefixCuts (2^48) 1920335873 9 Manual.Count131072.C014621.packed 128 cuts14621 = true := by
 decide +kernel
def pointBounds14621 : List (Nat × Nat × Nat) := [(1920361472,95932838070183,95933215878874),(1920421888,95933246711814,95933624520782)]
theorem point_links_checked14621 : (cuts14621.take 2).map (fun c => (1920335873-1+2*2^9*c.k,95932669215923+c.lower,95933047024501+c.upper)) = pointBounds14621 := by
 decide +kernel
def cuts14622 : List PrefixCut := [⟨15,105233872,105233942⟩,
⟨74,522643488,522643836⟩,
⟨128,898125000,898125603⟩]
theorem checked14622 : checkPrefixCuts (2^48) 1920466945 9 Manual.Count131072.C014622.packed 128 cuts14622 = true := by
 decide +kernel
def pointBounds14622 : List (Nat × Nat × Nat) := [(1920482304,95933654461140,95934032270382),(1920542720,95934071870756,95934449680276)]
theorem point_links_checked14622 : (cuts14622.take 2).map (fun c => (1920466945-1+2*2^9*c.k,95933549227268+c.lower,95933927036440+c.upper)) = pointBounds14622 := by
 decide +kernel
def cuts14623 : List PrefixCut := [⟨5,35759578,35759603⟩,
⟨64,445668733,445669040⟩,
⟨123,849556393,849556972⟩,
⟨128,884580896,884581500⟩]
theorem checked14623 : checkPrefixCuts (2^48) 1920598017 9 Manual.Count131072.C014623.packed 128 cuts14623 = true := by
 decide +kernel
def pointBounds14623 : List (Nat × Nat × Nat) := [(1920603136,95934483111846,95934860921646),(1920663552,95934893021001,95935270831083),(1920723968,95935296908661,95935674719015)]
theorem point_links_checked14623 : (cuts14623.take 3).map (fun c => (1920598017-1+2*2^9*c.k,95934447352268+c.lower,95934825162043+c.upper)) = pointBounds14623 := by
 decide +kernel
def cuts14624 : List PrefixCut := [⟨54,386728957,386729217⟩,
⟨113,800849111,800849652⟩,
⟨128,906941491,906942105⟩]
theorem checked14624 : checkPrefixCuts (2^48) 1920729089 9 Manual.Count131072.C014624.packed 128 cuts14624 = true := by
 decide +kernel
def pointBounds14624 : List (Nat × Nat × Nat) := [(1920784384,95935718662121,95936096472760),(1920844800,95936132782275,95936510593195)]
theorem point_links_checked14624 : (cuts14624.take 2).map (fun c => (1920729089-1+2*2^9*c.k,95935331933164+c.lower,95935709743543+c.upper)) = pointBounds14624 := by
 decide +kernel
def cuts14625 : List PrefixCut := [⟨44,301860305,301860510⟩,
⟨103,721815558,721816049⟩,
⟨128,896035984,896036590⟩]
theorem checked14625 : checkPrefixCuts (2^48) 1920860161 9 Manual.Count131072.C014625.packed 128 cuts14625 = true := by
 decide +kernel
def pointBounds14625 : List (Nat × Nat × Nat) := [(1920905216,95936540734960,95936918546158),(1920965632,95936960690213,95937338501697)]
theorem point_links_checked14625 : (cuts14625.take 2).map (fun c => (1920860161-1+2*2^9*c.k,95936238874655+c.lower,95936616685648+c.upper)) = pointBounds14625 := by
 decide +kernel
def cuts14626 : List PrefixCut := [⟨34,234878818,234878979⟩,
⟨93,645430336,645430772⟩,
⟨128,886451124,886451721⟩]
theorem checked14626 : checkPrefixCuts (2^48) 1920991233 9 Manual.Count131072.C014626.packed 128 cuts14626 = true := by
 decide +kernel
def pointBounds14626 : List (Nat × Nat × Nat) := [(1921026048,95937369789457,95937747601217),(1921086464,95937780340975,95938158153010)]
theorem point_links_checked14626 : (cuts14626.take 2).map (fun c => (1920991233-1+2*2^9*c.k,95937134910639+c.lower,95937512722238+c.upper)) = pointBounds14626 := by
 decide +kernel
def cuts14627 : List PrefixCut := [⟨24,166733987,166734099⟩,
⟨83,585757407,585757799⟩,
⟨128,903092942,903093549⟩]
theorem checked14627 : checkPrefixCuts (2^48) 1921122305 9 Manual.Count131072.C014627.packed 128 cuts14627 = true := by
 decide +kernel
def pointBounds14627 : List (Nat × Nat × Nat) := [(1921146880,95938188095750,95938565908058),(1921207296,95938607119170,95938984931758)]
theorem point_links_checked14627 : (cuts14627.take 2).map (fun c => (1921122305-1+2*2^9*c.k,95938021361763+c.lower,95938399173959+c.upper)) = pointBounds14627 := by
 decide +kernel
def cuts14628 : List PrefixCut := [⟨14,98744579,98744646⟩,
⟨73,517888127,517888477⟩,
⟨128,903177907,903178518⟩]
theorem checked14628 : checkPrefixCuts (2^48) 1921253377 9 Manual.Count131072.C014628.packed 128 cuts14628 = true := by
 decide +kernel
def pointBounds14628 : List (Nat × Nat × Nat) := [(1921267712,95939023199284,95939401012154),(1921328128,95939442342832,95939820155985)]
theorem point_links_checked14628 : (cuts14628.take 2).map (fun c => (1921253377-1+2*2^9*c.k,95938924454705+c.lower,95939302267508+c.upper)) = pointBounds14628 := by
 decide +kernel
def cuts14629 : List PrefixCut := [⟨4,29738630,29738650⟩,
⟨63,451053094,451053400⟩,
⟨122,864737002,864737584⟩,
⟨128,906778517,906779127⟩]
theorem checked14629 : checkPrefixCuts (2^48) 1921384449 9 Manual.Count131072.C014629.packed 128 cuts14629 = true := by
 decide +kernel
def pointBounds14629 : List (Nat × Nat × Nat) := [(1921388544,95939857371242,95940235184676),(1921448960,95940278685706,95940656499426),(1921509376,95940692369614,95941070183610)]
theorem point_links_checked14629 : (cuts14629.take 3).map (fun c => (1921384449-1+2*2^9*c.k,95939827632612+c.lower,95940205446026+c.upper)) = pointBounds14629 := by
 decide +kernel
def cuts14630 : List PrefixCut := [⟨53,374266108,374266360⟩,
⟨112,788363434,788363966⟩,
⟨128,900857384,900857991⟩]
theorem checked14630 : checkPrefixCuts (2^48) 1921515521 9 Manual.Count131072.C014630.packed 128 cuts14630 = true := by
 decide +kernel
def pointBounds14630 : List (Nat × Nat × Nat) := [(1921569792,95941108677237,95941486491513),(1921630208,95941522774563,95941900589119)]
theorem point_links_checked14630 : (cuts14630.take 2).map (fun c => (1921515521-1+2*2^9*c.k,95940734411129+c.lower,95941112225153+c.upper)) = pointBounds14630 := by
 decide +kernel
def cuts14631 : List PrefixCut := [⟨43,307156422,307156630⟩,
⟨102,721227675,721228165⟩,
⟨128,897573817,897574426⟩]
theorem checked14631 : checkPrefixCuts (2^48) 1921646593 9 Manual.Count131072.C014631.packed 128 cuts14631 = true := by
 decide +kernel
def pointBounds14631 : List (Nat × Nat × Nat) := [(1921690624,95941942424935,95942320239774),(1921751040,95942356496188,95942734311309)]
theorem point_links_checked14631 : (cuts14631.take 2).map (fun c => (1921646593-1+2*2^9*c.k,95941635268513+c.lower,95942013083144+c.upper)) = pointBounds14631 := by
 decide +kernel
def cuts14632 : List PrefixCut := [⟨33,225262571,225262726⟩,
⟨92,643701685,643702117⟩,
⟨128,896194065,896194669⟩]
theorem checked14632 : checkPrefixCuts (2^48) 1921777665 9 Manual.Count131072.C014632.packed 128 cuts14632 = true := by
 decide +kernel
def pointBounds14632 : List (Nat × Nat × Nat) := [(1921811456,95942758104901,95943135920296),(1921871872,95943176544015,95943554359687)]
theorem point_links_checked14632 : (cuts14632.take 2).map (fun c => (1921777665-1+2*2^9*c.k,95942532842330+c.lower,95942910657570+c.upper)) = pointBounds14632 := by
 decide +kernel
def cuts14633 : List PrefixCut := [⟨23,161393453,161393564⟩,
⟨82,573362349,573362734⟩,
⟨128,893643506,893644111⟩]
theorem checked14633 : checkPrefixCuts (2^48) 1921908737 9 Manual.Count131072.C014633.packed 128 cuts14633 = true := by
 decide +kernel
def pointBounds14633 : List (Nat × Nat × Nat) := [(1921932288,95943590429848,95943968245803),(1921992704,95944002398744,95944380214973)]
theorem point_links_checked14633 : (cuts14633.take 2).map (fun c => (1921908737-1+2*2^9*c.k,95943429036395+c.lower,95943806852239+c.upper)) = pointBounds14633 := by
 decide +kernel
def cuts14634 : List PrefixCut := [⟨13,86549239,86549297⟩,
⟨72,485166035,485166366⟩,
⟨128,880255966,880256563⟩]
theorem checked14634 : checkPrefixCuts (2^48) 1922039809 9 Manual.Count131072.C014634.packed 128 cuts14634 = true := by
 decide +kernel
def pointBounds14634 : List (Nat × Nat × Nat) := [(1922053120,95944409229140,95944787045647),(1922113536,95944807845936,95945185662716)]
theorem point_links_checked14634 : (cuts14634.take 2).map (fun c => (1922039809-1+2*2^9*c.k,95944322679901+c.lower,95944700496350+c.upper)) = pointBounds14634 := by
 decide +kernel
def cuts14635 : List PrefixCut := [⟨3,21233193,21233207⟩,
⟨62,440911292,440911585⟩,
⟨121,854719065,854719638⟩,
⟨128,901136177,901136782⟩]
theorem checked14635 : checkPrefixCuts (2^48) 1922170881 9 Manual.Count131072.C014635.packed 128 cuts14635 = true := by
 decide +kernel
def pointBounds14635 : List (Nat × Nat × Nat) := [(1922173952,95945224169060,95945601986120),(1922234368,95945643847159,95946021664498),(1922294784,95946057654932,95946435472551)]
theorem point_links_checked14635 : (cuts14635.take 3).map (fun c => (1922170881-1+2*2^9*c.k,95945202935867+c.lower,95945580752913+c.upper)) = pointBounds14635 := by
 decide +kernel
def cuts14636 : List PrefixCut := [⟨52,367084801,367085050⟩,
⟨111,783355641,783356171⟩,
⟨128,898878370,898878977⟩]
theorem checked14636 : checkPrefixCuts (2^48) 1922301953 9 Manual.Count131072.C014636.packed 128 cuts14636 = true := by
 decide +kernel
def pointBounds14636 : List (Nat × Nat × Nat) := [(1922355200,95946471156845,95946848974745),(1922415616,95946887427685,95947265245866)]
theorem point_links_checked14636 : (cuts14636.take 2).map (fun c => (1922301953-1+2*2^9*c.k,95946104072044+c.lower,95946481889695+c.upper)) = pointBounds14636 := by
 decide +kernel
def cuts14637 : List PrefixCut := [⟨42,296489054,296489251⟩,
⟨101,715954747,715955232⟩,
⟨128,904087783,904088393⟩]
theorem checked14637 : checkPrefixCuts (2^48) 1922433025 9 Manual.Count131072.C014637.packed 128 cuts14637 = true := by
 decide +kernel
def pointBounds14637 : List (Nat × Nat × Nat) := [(1922476032,95947299439468,95947677257923),(1922536448,95947718905161,95948096723904)]
theorem point_links_checked14637 : (cuts14637.take 2).map (fun c => (1922433025-1+2*2^9*c.k,95947002950414+c.lower,95947380768672+c.upper)) = pointBounds14637 := by
 decide +kernel
def cuts14638 : List PrefixCut := [⟨32,229709011,229709162⟩,
⟨91,638168324,638168750⟩,
⟨128,894510287,894510887⟩]
theorem checked14638 : checkPrefixCuts (2^48) 1922564097 9 Manual.Count131072.C014638.packed 128 cuts14638 = true := by
 decide +kernel
def pointBounds14638 : List (Nat × Nat × Nat) := [(1922596864,95948136747208,95948514566227),(1922657280,95948545206521,95948923025815)]
theorem point_links_checked14638 : (cuts14638.take 2).map (fun c => (1922564097-1+2*2^9*c.k,95947907038197+c.lower,95948284857065+c.upper)) = pointBounds14638 := by
 decide +kernel
def cuts14639 : List PrefixCut := [⟨22,158838751,158838856⟩,
⟨81,575031168,575031551⟩,
⟨128,900012242,900012843⟩]
theorem checked14639 : checkPrefixCuts (2^48) 1922695169 9 Manual.Count131072.C014639.packed 128 cuts14639 = true := by
 decide +kernel
def pointBounds14639 : List (Nat × Nat × Nat) := [(1922717696,95948960387235,95949338206808),(1922778112,95949376579652,95949754399503)]
theorem point_links_checked14639 : (cuts14639.take 2).map (fun c => (1922695169-1+2*2^9*c.k,95948801548484+c.lower,95949179367952+c.upper)) = pointBounds14639 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000144
