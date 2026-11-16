import PlattAssemblyKernel
import PlattCertificates.Count131072.C011600
import PlattCertificates.Count131072.C011601
import PlattCertificates.Count131072.C011602
import PlattCertificates.Count131072.C011603
import PlattCertificates.Count131072.C011604
import PlattCertificates.Count131072.C011605
import PlattCertificates.Count131072.C011606
import PlattCertificates.Count131072.C011607
import PlattCertificates.Count131072.C011608
import PlattCertificates.Count131072.C011609
import PlattCertificates.Count131072.C011610
import PlattCertificates.Count131072.C011611
import PlattCertificates.Count131072.C011612
import PlattCertificates.Count131072.C011613
import PlattCertificates.Count131072.C011614
import PlattCertificates.Count131072.C011615
import PlattCertificates.Count131072.C011616
import PlattCertificates.Count131072.C011617
import PlattCertificates.Count131072.C011618
import PlattCertificates.Count131072.C011619
import PlattCertificates.Count131072.C011620
import PlattCertificates.Count131072.C011621
import PlattCertificates.Count131072.C011622
import PlattCertificates.Count131072.C011623
import PlattCertificates.Count131072.C011624
import PlattCertificates.Count131072.C011625
import PlattCertificates.Count131072.C011626
import PlattCertificates.Count131072.C011627
import PlattCertificates.Count131072.C011628
import PlattCertificates.Count131072.C011629
import PlattCertificates.Count131072.C011630
import PlattCertificates.Count131072.C011631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11600 : List PrefixCut := [⟨17,147534708,147534823⟩,
⟨64,572218848,572219301⟩,
⟨111,993750745,993751530⟩,
⟨128,1142197672,1142198574⟩]
theorem checked11600 : checkPrefixCuts (2^48) 1524367361 9 Manual.Count131072.C011600.packed 128 cuts11600 = true := by
 decide +kernel
def pointBounds11600 : List (Nat × Nat × Nat) := [(1524384768,92875711723868,92876087311615),(1524432896,92876136408008,92876511996093),(1524481024,92876557939905,92876933528322)]
theorem point_links_checked11600 : (cuts11600.take 3).map (fun c => (1524367361-1+2*2^9*c.k,92875564189160+c.lower,92875939776792+c.upper)) = pointBounds11600 := by
 decide +kernel
def cuts11601 : List PrefixCut := [⟨30,272517616,272517827⟩,
⟨77,685714580,685715117⟩,
⟨124,1109237306,1109238175⟩,
⟨128,1145053349,1145054244⟩]
theorem checked11601 : checkPrefixCuts (2^48) 1524498433 9 Manual.Count131072.C011601.packed 128 cuts11601 = true := by
 decide +kernel
def pointBounds11601 : List (Nat × Nat × Nat) := [(1524529152,92876978904448,92877354493193),(1524577280,92877392101412,92877767690483),(1524625408,92877815624138,92878191213541)]
theorem point_links_checked11601 : (cuts11601.take 3).map (fun c => (1524498433-1+2*2^9*c.k,92876706386832+c.lower,92877081975366+c.upper)) = pointBounds11601 := by
 decide +kernel
def cuts11602 : List PrefixCut := [⟨43,381601004,381601302⟩,
⟨90,801589321,801589949⟩,
⟨128,1141077883,1141078774⟩]
theorem checked11602 : checkPrefixCuts (2^48) 1524629505 9 Manual.Count131072.C011602.packed 128 cuts11602 = true := by
 decide +kernel
def pointBounds11602 : List (Nat × Nat × Nat) := [(1524673536,92878233041185,92878608630912),(1524721664,92878653029502,92879028619559)]
theorem point_links_checked11602 : (cuts11602.take 2).map (fun c => (1524629505-1+2*2^9*c.k,92877851440181+c.lower,92878227029610+c.upper)) = pointBounds11602 := by
 decide +kernel
def cuts11603 : List PrefixCut := [⟨9,80671123,80671186⟩,
⟨56,501186921,501187311⟩,
⟨103,923904534,923905258⟩,
⟨128,1147441011,1147441913⟩]
theorem checked11603 : checkPrefixCuts (2^48) 1524760577 9 Manual.Count131072.C011603.packed 128 cuts11603 = true := by
 decide +kernel
def pointBounds11603 : List (Nat × Nat × Nat) := [(1524769792,92879073189187,92879448779570),(1524817920,92879493704985,92879869295695),(1524866048,92879916422598,92880292013642)]
theorem point_links_checked11603 : (cuts11603.take 3).map (fun c => (1524760577-1+2*2^9*c.k,92878992518064+c.lower,92879368108384+c.upper)) = pointBounds11603 := by
 decide +kernel
def cuts11604 : List PrefixCut := [⟨22,191784277,191784428⟩,
⟨69,609491464,609491945⟩,
⟨116,1028661978,1028662790⟩,
⟨128,1139774135,1139775035⟩]
theorem checked11604 : checkPrefixCuts (2^48) 1524891649 9 Manual.Count131072.C011604.packed 128 cuts11604 = true := by
 decide +kernel
def pointBounds11604 : List (Nat × Nat × Nat) := [(1524914176,92880331743352,92880707334725),(1524962304,92880749450539,92881125042242),(1525010432,92881168621053,92881544213087)]
theorem point_links_checked11604 : (cuts11604.take 3).map (fun c => (1524891649-1+2*2^9*c.k,92880139959075+c.lower,92880515550297+c.upper)) = pointBounds11604 := by
 decide +kernel
def cuts11605 : List PrefixCut := [⟨35,312105758,312106005⟩,
⟨82,732541792,732542362⟩,
⟨128,1148904516,1148905414⟩]
theorem checked11605 : checkPrefixCuts (2^48) 1525022721 9 Manual.Count131072.C011605.packed 128 cuts11605 = true := by
 decide +kernel
def pointBounds11605 : List (Nat × Nat × Nat) := [(1525058560,92881591838968,92881967431337),(1525106688,92882012275002,92882387867694)]
theorem point_links_checked11605 : (cuts11605.take 2).map (fun c => (1525022721-1+2*2^9*c.k,92881279733210+c.lower,92881655325332+c.upper)) = pointBounds11605 := by
 decide +kernel
def cuts11606 : List PrefixCut := [⟨1,9781416,9781423⟩,
⟨48,418379603,418379929⟩,
⟨95,827149487,827150136⟩,
⟨128,1120754623,1120755502⟩]
theorem checked11606 : checkPrefixCuts (2^48) 1525153793 9 Manual.Count131072.C011606.packed 128 cuts11606 = true := by
 decide +kernel
def pointBounds11606 : List (Nat × Nat × Nat) := [(1525154816,92882438419142,92882814012169),(1525202944,92882847017329,92883222610675),(1525251072,92883255787213,92883631380882)]
theorem point_links_checked11606 : (cuts11606.take 3).map (fun c => (1525153793-1+2*2^9*c.k,92882428637726+c.lower,92882804230746+c.upper)) = pointBounds11606 := by
 decide +kernel
def cuts11607 : List PrefixCut := [⟨14,126408759,126408858⟩,
⟨61,550100075,550100509⟩,
⟨108,975254366,975255131⟩,
⟨128,1151844415,1151845314⟩]
theorem checked11607 : checkPrefixCuts (2^48) 1525284865 9 Manual.Count131072.C011607.packed 128 cuts11607 = true := by
 decide +kernel
def pointBounds11607 : List (Nat × Nat × Nat) := [(1525299200,92883675801108,92884051395106),(1525347328,92884099492424,92884475086757),(1525395456,92884524646715,92884900241379)]
theorem point_links_checked11607 : (cuts11607.take 3).map (fun c => (1525284865-1+2*2^9*c.k,92883549392349+c.lower,92883924986248+c.upper)) = pointBounds11607 := by
 decide +kernel
def cuts11608 : List PrefixCut := [⟨27,241354353,241354542⟩,
⟨74,667588912,667589430⟩,
⟨121,1086429543,1086430387⟩,
⟨128,1155989035,1155989933⟩]
theorem checked11608 : checkPrefixCuts (2^48) 1525415937 9 Manual.Count131072.C011608.packed 128 cuts11608 = true := by
 decide +kernel
def pointBounds11608 : List (Nat × Nat × Nat) := [(1525443584,92884942591117,92885318186104),(1525491712,92885368825676,92885744420992),(1525539840,92885787666307,92886163261949)]
theorem point_links_checked11608 : (cuts11608.take 3).map (fun c => (1525415937-1+2*2^9*c.k,92884701236764+c.lower,92885076831562+c.upper)) = pointBounds11608 := by
 decide +kernel
def cuts11609 : List PrefixCut := [⟨40,352035593,352035866⟩,
⟨87,769742847,769743449⟩,
⟨128,1128952917,1128953798⟩]
theorem checked11609 : checkPrefixCuts (2^48) 1525547009 9 Manual.Count131072.C011609.packed 128 cuts11609 = true := by
 decide +kernel
def pointBounds11609 : List (Nat × Nat × Nat) := [(1525587968,92886209261392,92886584857361),(1525636096,92886626968646,92887002564944)]
theorem point_links_checked11609 : (cuts11609.take 2).map (fun c => (1525547009-1+2*2^9*c.k,92885857225799+c.lower,92886232821495+c.upper)) = pointBounds11609 := by
 decide +kernel
def cuts11610 : List PrefixCut := [⟨6,50366117,50366158⟩,
⟨53,475242062,475242436⟩,
⟨100,889220094,889220796⟩,
⟨128,1141954313,1141955210⟩]
theorem checked11610 : checkPrefixCuts (2^48) 1525678081 9 Manual.Count131072.C011610.packed 128 cuts11610 = true := by
 decide +kernel
def pointBounds11610 : List (Nat × Nat × Nat) := [(1525684224,92887036544833,92887412141451),(1525732352,92887461420778,92887837017729),(1525780480,92887875398810,92888250996089)]
theorem point_links_checked11610 : (cuts11610.take 3).map (fun c => (1525678081-1+2*2^9*c.k,92886986178716+c.lower,92887361775293+c.upper)) = pointBounds11610 := by
 decide +kernel
def cuts11611 : List PrefixCut := [⟨19,170270091,170270224⟩,
⟨66,586620146,586620603⟩,
⟨113,1011442447,1011443234⟩,
⟨128,1147759057,1147759951⟩]
theorem checked11611 : checkPrefixCuts (2^48) 1525809153 9 Manual.Count131072.C011611.packed 128 cuts11611 = true := by
 decide +kernel
def pointBounds11611 : List (Nat × Nat × Nat) := [(1525828608,92888298403120,92888674000727),(1525876736,92888714753175,92889090351106),(1525924864,92889139575476,92889515173737)]
theorem point_links_checked11611 : (cuts11611.take 3).map (fun c => (1525809153-1+2*2^9*c.k,92888128133029+c.lower,92888503730503+c.upper)) = pointBounds11611 := by
 decide +kernel
def cuts11612 : List PrefixCut := [⟨32,280929449,280929666⟩,
⟨79,698346754,698347302⟩,
⟨126,1123313305,1123314183⟩,
⟨128,1143048840,1143049732⟩]
theorem checked11612 : checkPrefixCuts (2^48) 1525940225 9 Manual.Count131072.C011612.packed 128 cuts11612 = true := by
 decide +kernel
def pointBounds11612 : List (Nat × Nat × Nat) := [(1525972992,92889556821535,92889932420120),(1526021120,92889974238840,92890349837756),(1526069248,92890399205391,92890774804637)]
theorem point_links_checked11612 : (cuts11612.take 3).map (fun c => (1525940225-1+2*2^9*c.k,92889275892086+c.lower,92889651490454+c.upper)) = pointBounds11612 := by
 decide +kernel
def cuts11613 : List PrefixCut := [⟨45,404479986,404480304⟩,
⟨92,832001761,832002417⟩,
⟨128,1147562255,1147563160⟩]
theorem checked11613 : checkPrefixCuts (2^48) 1526071297 9 Manual.Count131072.C011613.packed 128 cuts11613 = true := by
 decide +kernel
def pointBounds11613 : List (Nat × Nat × Nat) := [(1526117376,92890823420912,92891199020490),(1526165504,92891250942687,92891626542603)]
theorem point_links_checked11613 : (cuts11613.take 2).map (fun c => (1526071297-1+2*2^9*c.k,92890418940926+c.lower,92890794540186+c.upper)) = pointBounds11613 := by
 decide +kernel
def cuts11614 : List PrefixCut := [⟨11,97562193,97562271⟩,
⟨58,521552999,521553408⟩,
⟨105,932067872,932068603⟩,
⟨128,1142668497,1142669393⟩]
theorem checked11614 : checkPrefixCuts (2^48) 1526202369 9 Manual.Count131072.C011614.packed 128 cuts11614 = true := by
 decide +kernel
def pointBounds11614 : List (Nat × Nat × Nat) := [(1526213632,92891664065374,92892039665617),(1526261760,92892088056180,92892463656754),(1526309888,92892498571053,92892874171949)]
theorem point_links_checked11614 : (cuts11614.take 3).map (fun c => (1526202369-1+2*2^9*c.k,92891566503181+c.lower,92891942103346+c.upper)) = pointBounds11614 := by
 decide +kernel
def cuts11615 : List PrefixCut := [⟨24,214838752,214838918⟩,
⟨71,640449089,640449590⟩,
⟨118,1050003180,1050004003⟩,
⟨128,1139251431,1139252325⟩]
theorem checked11615 : checkPrefixCuts (2^48) 1526333441 9 Manual.Count131072.C011615.packed 128 cuts11615 = true := by
 decide +kernel
def pointBounds11615 : List (Nat × Nat × Nat) := [(1526358016,92892924010430,92893299611657),(1526406144,92893349620767,92893725222329),(1526454272,92893759174858,92894134776742)]
theorem point_links_checked11615 : (cuts11615.take 3).map (fun c => (1526333441-1+2*2^9*c.k,92892709171678+c.lower,92893084772739+c.upper)) = pointBounds11615 := by
 decide +kernel
def cuts11616 : List PrefixCut := [⟨37,338179194,338179457⟩,
⟨84,755636167,755636754⟩,
⟨128,1147266700,1147267592⟩]
theorem checked11616 : checkPrefixCuts (2^48) 1526464513 9 Manual.Count131072.C011616.packed 128 cuts11616 = true := by
 decide +kernel
def pointBounds11616 : List (Nat × Nat × Nat) := [(1526502400,92894186602303,92894562204521),(1526550528,92894604059276,92894979661818)]
theorem point_links_checked11616 : (cuts11616.take 2).map (fun c => (1526464513-1+2*2^9*c.k,92893848423109+c.lower,92894224025064+c.upper)) = pointBounds11616 := by
 decide +kernel
def cuts11617 : List PrefixCut := [⟨3,26182044,26182063⟩,
⟨50,439740734,439741076⟩,
⟨97,861030074,861030743⟩,
⟨128,1144955031,1144955922⟩]
theorem checked11617 : checkPrefixCuts (2^48) 1526595585 9 Manual.Count131072.C011617.packed 128 cuts11617 = true := by
 decide +kernel
def pointBounds11617 : List (Nat × Nat × Nat) := [(1526598656,92895021871853,92895397474719),(1526646784,92895435430543,92895811033732),(1526694912,92895856719883,92896232323399)]
theorem point_links_checked11617 : (cuts11617.take 3).map (fun c => (1526595585-1+2*2^9*c.k,92894995689809+c.lower,92895371292656+c.upper)) = pointBounds11617 := by
 decide +kernel
def cuts11618 : List PrefixCut := [⟨16,144541330,144541443⟩,
⟨63,559351387,559351824⟩,
⟨110,978388593,978389357⟩,
⟨128,1143013336,1143014227⟩]
theorem checked11618 : checkPrefixCuts (2^48) 1526726657 9 Manual.Count131072.C011618.packed 128 cuts11618 = true := by
 decide +kernel
def pointBounds11618 : List (Nat × Nat × Nat) := [(1526743040,92896285186170,92896660790021),(1526791168,92896699996227,92897075600402),(1526839296,92897119033433,92897494637935)]
theorem point_links_checked11618 : (cuts11618.take 3).map (fun c => (1526726657-1+2*2^9*c.k,92896140644840+c.lower,92896516248578+c.upper)) = pointBounds11618 := by
 decide +kernel
def cuts11619 : List PrefixCut := [⟨29,256242759,256242955⟩,
⟨76,675253516,675254040⟩,
⟨123,1090011281,1090012131⟩,
⟨128,1132776677,1132777561⟩]
theorem checked11619 : checkPrefixCuts (2^48) 1526857729 9 Manual.Count131072.C011619.packed 128 cuts11619 = true := by
 decide +kernel
def pointBounds11619 : List (Nat × Nat × Nat) := [(1526887424,92897539900935,92897915505760),(1526935552,92897958911692,92898334516845),(1526983680,92898373669457,92898749274936)]
theorem point_links_checked11619 : (cuts11619.take 3).map (fun c => (1526857729-1+2*2^9*c.k,92897283658176+c.lower,92897659262805+c.upper)) = pointBounds11619 := by
 decide +kernel
def cuts11620 : List PrefixCut := [⟨42,372901061,372901354⟩,
⟨89,795927378,795927999⟩,
⟨128,1150927396,1150928291⟩]
theorem checked11620 : checkPrefixCuts (2^48) 1526988801 9 Manual.Count131072.C011620.packed 128 cuts11620 = true := by
 decide +kernel
def pointBounds11620 : List (Nat × Nat × Nat) := [(1527031808,92898789335914,92899164941720),(1527079936,92899212362231,92899587968365)]
theorem point_links_checked11620 : (cuts11620.take 2).map (fun c => (1526988801-1+2*2^9*c.k,92898416434853+c.lower,92898792040366+c.upper)) = pointBounds11620 := by
 decide +kernel
def cuts11621 : List PrefixCut := [⟨8,76675864,76675925⟩,
⟨55,499306877,499307268⟩,
⟨102,910681895,910682612⟩,
⟨128,1151934833,1151935739⟩]
theorem checked11621 : checkPrefixCuts (2^48) 1527119873 9 Manual.Count131072.C011621.packed 128 cuts11621 = true := by
 decide +kernel
def pointBounds11621 : List (Nat × Nat × Nat) := [(1527128064,92899644038113,92900019644582),(1527176192,92900066669126,92900442275925),(1527224320,92900478044144,92900853651269)]
theorem point_links_checked11621 : (cuts11621.take 3).map (fun c => (1527119873-1+2*2^9*c.k,92899567362249+c.lower,92899942968657+c.upper)) = pointBounds11621 := by
 decide +kernel
def cuts11622 : List PrefixCut := [⟨21,183378827,183378969⟩,
⟨68,599335165,599335628⟩,
⟨115,1023387295,1023388091⟩,
⟨128,1140040727,1140041615⟩]
theorem checked11622 : checkPrefixCuts (2^48) 1527250945 9 Manual.Count131072.C011622.packed 128 cuts11622 = true := by
 decide +kernel
def pointBounds11622 : List (Nat × Nat × Nat) := [(1527272448,92900902675909,92901278283365),(1527320576,92901318632247,92901694240024),(1527368704,92901742684377,92902118292487)]
theorem point_links_checked11622 : (cuts11622.take 3).map (fun c => (1527250945-1+2*2^9*c.k,92900719297082+c.lower,92901094904396+c.upper)) = pointBounds11622 := by
 decide +kernel
def cuts11623 : List PrefixCut := [⟨34,305911028,305911269⟩,
⟨81,727540695,727541266⟩,
⟨128,1152474137,1152475043⟩]
theorem checked11623 : checkPrefixCuts (2^48) 1527382017 9 Manual.Count131072.C011623.packed 128 cuts11623 = true := by
 decide +kernel
def pointBounds11623 : List (Nat × Nat × Nat) := [(1527416832,92902165248837,92902540857280),(1527464960,92902586878504,92902962487277),(1527513088,92903011811946,92903387421054)]
theorem point_links_checked11623 : (cuts11623.take 3).map (fun c => (1527382017-1+2*2^9*c.k,92901859337809+c.lower,92902234946011+c.upper)) = pointBounds11623 := by
 decide +kernel
def cuts11624 : List PrefixCut := [⟨47,418102091,418102419⟩,
⟨94,835085470,835086125⟩,
⟨128,1138002872,1138003765⟩]
theorem checked11624 : checkPrefixCuts (2^48) 1527513089 9 Manual.Count131072.C011624.packed 128 cuts11624 = true := by
 decide +kernel
def pointBounds11624 : List (Nat × Nat × Nat) := [(1527561216,92903429914037,92903805523473),(1527609344,92903846897416,92904222507179)]
theorem point_links_checked11624 : (cuts11624.take 2).map (fun c => (1527513089-1+2*2^9*c.k,92903011811946+c.lower,92903387421054+c.upper)) = pointBounds11624 := by
 decide +kernel
def cuts11625 : List PrefixCut := [⟨13,113315852,113315941⟩,
⟨60,536168845,536169262⟩,
⟨107,954402492,954403236⟩,
⟨128,1135694313,1135695197⟩]
theorem checked11625 : checkPrefixCuts (2^48) 1527644161 9 Manual.Count131072.C011625.packed 128 cuts11625 = true := by
 decide +kernel
def pointBounds11625 : List (Nat × Nat × Nat) := [(1527657472,92904263130670,92904638740760),(1527705600,92904685983663,92905061594081),(1527753728,92905104217310,92905479828055)]
theorem point_links_checked11625 : (cuts11625.take 3).map (fun c => (1527644161-1+2*2^9*c.k,92904149814818+c.lower,92904525424819+c.upper)) = pointBounds11625 := by
 decide +kernel
def cuts11626 : List PrefixCut := [⟨26,237297006,237297193⟩,
⟨73,671900986,671901513⟩,
⟨120,1094884957,1094885816⟩,
⟨128,1162863278,1162864189⟩]
theorem checked11626 : checkPrefixCuts (2^48) 1527775233 9 Manual.Count131072.C011626.packed 128 cuts11626 = true := by
 decide +kernel
def pointBounds11626 : List (Nat × Nat × Nat) := [(1527801856,92905522806137,92905898417209),(1527849984,92905957410117,92906333021529),(1527898112,92906380394088,92906756005832)]
theorem point_links_checked11626 : (cuts11626.take 3).map (fun c => (1527775233-1+2*2^9*c.k,92905285509131+c.lower,92905661120016+c.upper)) = pointBounds11626 := by
 decide +kernel
def cuts11627 : List PrefixCut := [⟨39,346149754,346150028⟩,
⟨86,764685923,764686525⟩,
⟨128,1136788826,1136789720⟩]
theorem checked11627 : checkPrefixCuts (2^48) 1527906305 9 Manual.Count131072.C011627.packed 128 cuts11627 = true := by
 decide +kernel
def pointBounds11627 : List (Nat × Nat × Nat) := [(1527946240,92906794522163,92907170134233),(1527994368,92907213058332,92907588670730)]
theorem point_links_checked11627 : (cuts11627.take 2).map (fun c => (1527906305-1+2*2^9*c.k,92906448372409+c.lower,92906823984205+c.upper)) = pointBounds11627 := by
 decide +kernel
def cuts11628 : List PrefixCut := [⟨5,45314797,45314831⟩,
⟨52,464561494,464561857⟩,
⟨99,887847272,887847968⟩,
⟨128,1138349462,1138350356⟩]
theorem checked11628 : checkPrefixCuts (2^48) 1528037377 9 Manual.Count131072.C011628.packed 128 cuts11628 = true := by
 decide +kernel
def pointBounds11628 : List (Nat × Nat × Nat) := [(1528042496,92907630476032,92908006088756),(1528090624,92908049722729,92908425335782),(1528138752,92908473008507,92908848621893)]
theorem point_links_checked11628 : (cuts11628.take 3).map (fun c => (1528037377-1+2*2^9*c.k,92907585161235+c.lower,92907960773925+c.upper)) = pointBounds11628 := by
 decide +kernel
def cuts11629 : List PrefixCut := [⟨18,164481569,164481695⟩,
⟨65,589766762,589767223⟩,
⟨112,1019643076,1019643871⟩,
⟨128,1158143567,1158144471⟩]
theorem checked11629 : checkPrefixCuts (2^48) 1528168449 9 Manual.Count131072.C011629.packed 128 cuts11629 = true := by
 decide +kernel
def pointBounds11629 : List (Nat × Nat × Nat) := [(1528186880,92908887992266,92909263605976),(1528235008,92909313277459,92909688891504),(1528283136,92909743153773,92910118768152)]
theorem point_links_checked11629 : (cuts11629.take 3).map (fun c => (1528168449-1+2*2^9*c.k,92908723510697+c.lower,92909099124281+c.upper)) = pointBounds11629 := by
 decide +kernel
def cuts11630 : List PrefixCut := [⟨31,277733322,277733540⟩,
⟨78,695611620,695612166⟩,
⟨125,1117159982,1117160853⟩,
⟨128,1141284888,1141285779⟩]
theorem checked11630 : checkPrefixCuts (2^48) 1528299521 9 Manual.Count131072.C011630.packed 128 cuts11630 = true := by
 decide +kernel
def pointBounds11630 : List (Nat × Nat × Nat) := [(1528331264,92910159387586,92910535002292),(1528379392,92910577265884,92910952880918),(1528427520,92910998814246,92911374429605)]
theorem point_links_checked11630 : (cuts11630.take 3).map (fun c => (1528299521-1+2*2^9*c.k,92909881654264+c.lower,92910257268752+c.upper)) = pointBounds11630 := by
 decide +kernel
def cuts11631 : List PrefixCut := [⟨44,397041856,397042166⟩,
⟨91,813775696,813776329⟩,
⟨128,1145974952,1145975846⟩]
theorem checked11631 : checkPrefixCuts (2^48) 1528430593 9 Manual.Count131072.C011631.packed 128 cuts11631 = true := by
 decide +kernel
def pointBounds11631 : List (Nat × Nat × Nat) := [(1528475648,92911419981008,92911795596697),(1528523776,92911836714848,92912212330860)]
theorem point_links_checked11631 : (cuts11631.take 2).map (fun c => (1528430593-1+2*2^9*c.k,92911022939152+c.lower,92911398554531+c.upper)) = pointBounds11631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000050
