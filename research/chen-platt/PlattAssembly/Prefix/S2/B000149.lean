import PlattAssemblyKernel
import PlattCertificates.Count131072.C014768
import PlattCertificates.Count131072.C014769
import PlattCertificates.Count131072.C014770
import PlattCertificates.Count131072.C014771
import PlattCertificates.Count131072.C014772
import PlattCertificates.Count131072.C014773
import PlattCertificates.Count131072.C014774
import PlattCertificates.Count131072.C014775
import PlattCertificates.Count131072.C014776
import PlattCertificates.Count131072.C014777
import PlattCertificates.Count131072.C014778
import PlattCertificates.Count131072.C014779
import PlattCertificates.Count131072.C014780
import PlattCertificates.Count131072.C014781
import PlattCertificates.Count131072.C014782
import PlattCertificates.Count131072.C014783
import PlattCertificates.Count131072.C014784
import PlattCertificates.Count131072.C014785
import PlattCertificates.Count131072.C014786
import PlattCertificates.Count131072.C014787
import PlattCertificates.Count131072.C014788
import PlattCertificates.Count131072.C014789
import PlattCertificates.Count131072.C014790
import PlattCertificates.Count131072.C014791
import PlattCertificates.Count131072.C014792
import PlattCertificates.Count131072.C014793
import PlattCertificates.Count131072.C014794
import PlattCertificates.Count131072.C014795
import PlattCertificates.Count131072.C014796
import PlattCertificates.Count131072.C014797
import PlattCertificates.Count131072.C014798
import PlattCertificates.Count131072.C014799
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000149
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14768 : List PrefixCut := [⟨14,101003004,101003073⟩,
⟨74,517197005,517197355⟩,
⟨128,892746967,892747569⟩]
theorem checked14768 : checkPrefixCuts (2^48) 1939603457 9 Manual.Count131072.C014768.packed 128 cuts14768 = true := by
 decide +kernel
def pointBounds14768 : List (Nat × Nat × Nat) := [(1939617792,96064167565882,96064545462995),(1939679232,96064583759883,96064961657277)]
theorem point_links_checked14768 : (cuts14768.take 2).map (fun c => (1939603457-1+2*2^9*c.k,96064066562878+c.lower,96064444459922+c.upper)) = pointBounds14768 := by
 decide +kernel
def cuts14769 : List PrefixCut := [⟨6,40050299,40050325⟩,
⟨66,453170676,453170982⟩,
⟨126,871646754,871647338⟩,
⟨128,884995979,884996572⟩]
theorem checked14769 : checkPrefixCuts (2^48) 1939734529 9 Manual.Count131072.C014769.packed 128 cuts14769 = true := by
 decide +kernel
def pointBounds14769 : List (Nat × Nat × Nat) := [(1939740672,96064999360144,96065377257816),(1939802112,96065412480521,96065790378473),(1939863552,96065830956599,96066208854829)]
theorem point_links_checked14769 : (cuts14769.take 3).map (fun c => (1939734529-1+2*2^9*c.k,96064959309845+c.lower,96065337207491+c.upper)) = pointBounds14769 := by
 decide +kernel
def cuts14770 : List PrefixCut := [⟨58,390603675,390603938⟩,
⟨118,815872608,815873153⟩,
⟨128,886241634,886242226⟩]
theorem checked14770 : checkPrefixCuts (2^48) 1939865601 9 Manual.Count131072.C014770.packed 128 cuts14770 = true := by
 decide +kernel
def pointBounds14770 : List (Nat × Nat × Nat) := [(1939924992,96066234909499,96066612808001),(1939986432,96066660178432,96067038077216)]
theorem point_links_checked14770 : (cuts14770.take 2).map (fun c => (1939865601-1+2*2^9*c.k,96065844305824+c.lower,96066222204063+c.upper)) = pointBounds14770 := by
 decide +kernel
def cuts14771 : List PrefixCut := [⟨50,343279320,343279550⟩,
⟨110,757785103,757785610⟩,
⟨128,881249273,881249861⟩]
theorem checked14771 : checkPrefixCuts (2^48) 1939996673 9 Manual.Count131072.C014771.packed 128 cuts14771 = true := by
 decide +kernel
def pointBounds14771 : List (Nat × Nat × Nat) := [(1940047872,96067073826778,96067451725839),(1940109312,96067488332561,96067866231899)]
theorem point_links_checked14771 : (cuts14771.take 2).map (fun c => (1939996673-1+2*2^9*c.k,96066730547458+c.lower,96067108446289+c.upper)) = pointBounds14771 := by
 decide +kernel
def cuts14772 : List PrefixCut := [⟨42,294945597,294945793⟩,
⟨102,719290284,719290762⟩,
⟨128,899179310,899179909⟩]
theorem checked14772 : checkPrefixCuts (2^48) 1940127745 9 Manual.Count131072.C014772.packed 128 cuts14772 = true := by
 decide +kernel
def pointBounds14772 : List (Nat × Nat × Nat) := [(1940170752,96067906742328,96068284641943),(1940232192,96068331087015,96068708986912)]
theorem point_links_checked14772 : (cuts14772.take 2).map (fun c => (1940127745-1+2*2^9*c.k,96067611796731+c.lower,96067989696150+c.upper)) = pointBounds14772 := by
 decide +kernel
def cuts14773 : List PrefixCut := [⟨34,230370404,230370564⟩,
⟨94,644098326,644098769⟩,
⟨128,879244327,879244930⟩]
theorem checked14773 : checkPrefixCuts (2^48) 1940258817 9 Manual.Count131072.C014773.packed 128 cuts14773 = true := by
 decide +kernel
def pointBounds14773 : List (Nat × Nat × Nat) := [(1940293632,96068741346445,96069119246623),(1940355072,96069155074367,96069532974828)]
theorem point_links_checked14773 : (cuts14773.take 2).map (fun c => (1940258817-1+2*2^9*c.k,96068510976041+c.lower,96068888876059+c.upper)) = pointBounds14773 := by
 decide +kernel
def cuts14774 : List PrefixCut := [⟨26,176683090,176683207⟩,
⟨86,593866206,593866606⟩,
⟨128,889483879,889484474⟩]
theorem checked14774 : checkPrefixCuts (2^48) 1940389889 9 Manual.Count131072.C014774.packed 128 cuts14774 = true := by
 decide +kernel
def pointBounds14774 : List (Nat × Nat × Nat) := [(1940416512,96069566903458,96069944804196),(1940477952,96069984086574,96070361987595)]
theorem point_links_checked14774 : (cuts14774.take 2).map (fun c => (1940389889-1+2*2^9*c.k,96069390220368+c.lower,96069768120989+c.upper)) = pointBounds14774 := by
 decide +kernel
def cuts14775 : List PrefixCut := [⟨18,125033518,125033605⟩,
⟨78,549152419,549152793⟩,
⟨128,899141876,899142489⟩]
theorem checked14775 : checkPrefixCuts (2^48) 1940520961 9 Manual.Count131072.C014775.packed 128 cuts14775 = true := by
 decide +kernel
def pointBounds14775 : List (Nat × Nat × Nat) := [(1940539392,96070404737765,96070782639068),(1940600832,96070828856666,96071206758256)]
theorem point_links_checked14775 : (cuts14775.take 2).map (fun c => (1940520961-1+2*2^9*c.k,96070279704247+c.lower,96070657605463+c.upper)) = pointBounds14775 := by
 decide +kernel
def cuts14776 : List PrefixCut := [⟨10,70054811,70054857⟩,
⟨70,499658347,499658683⟩,
⟨128,905607992,905608595⟩]
theorem checked14776 : checkPrefixCuts (2^48) 1940652033 9 Manual.Count131072.C014776.packed 128 cuts14776 = true := by
 decide +kernel
def pointBounds14776 : List (Nat × Nat × Nat) := [(1940662272,96071248900934,96071626802809),(1940723712,96071678504470,96072056406635)]
theorem point_links_checked14776 : (cuts14776.take 2).map (fun c => (1940652033-1+2*2^9*c.k,96071178846123+c.lower,96071556747952+c.upper)) = pointBounds14776 := by
 decide +kernel
def cuts14777 : List PrefixCut := [⟨2,13632962,13632972⟩,
⟨62,428271310,428271600⟩,
⟨122,832019629,832020194⟩,
⟨128,874656111,874656704⟩]
theorem checked14777 : checkPrefixCuts (2^48) 1940783105 9 Manual.Count131072.C014777.packed 128 cuts14777 = true := by
 decide +kernel
def pointBounds14777 : List (Nat × Nat × Nat) := [(1940785152,96072098087077,96072475989519),(1940846592,96072512725425,96072890628147),(1940908032,96072916473744,96073294376741)]
theorem point_links_checked14777 : (cuts14777.take 3).map (fun c => (1940783105-1+2*2^9*c.k,96072084454115+c.lower,96072462356547+c.upper)) = pointBounds14777 := by
 decide +kernel
def cuts14778 : List PrefixCut := [⟨54,370380407,370380658⟩,
⟨114,790634987,790635520⟩,
⟨128,887938409,887939010⟩]
theorem checked14778 : checkPrefixCuts (2^48) 1940914177 9 Manual.Count131072.C014778.packed 128 cuts14778 = true := by
 decide +kernel
def pointBounds14778 : List (Nat × Nat × Nat) := [(1940969472,96073329490633,96073707393909),(1941030912,96073749745213,96074127648771)]
theorem point_links_checked14778 : (cuts14778.take 2).map (fun c => (1940914177-1+2*2^9*c.k,96072959110226+c.lower,96073337013251+c.upper)) = pointBounds14778 := by
 decide +kernel
def cuts14779 : List PrefixCut := [⟨46,320907718,320907933⟩,
⟨106,740120600,740121092⟩,
⟨128,889618749,889619341⟩]
theorem checked14779 : checkPrefixCuts (2^48) 1941045249 9 Manual.Count131072.C014779.packed 128 cuts14779 = true := by
 decide +kernel
def pointBounds14779 : List (Nat × Nat × Nat) := [(1941092352,96074167956353,96074545860194),(1941153792,96074587169235,96074965073353)]
theorem point_links_checked14779 : (cuts14779.take 2).map (fun c => (1941045249-1+2*2^9*c.k,96073847048635+c.lower,96074224952261+c.upper)) = pointBounds14779 := by
 decide +kernel
def cuts14780 : List PrefixCut := [⟨38,269121446,269121624⟩,
⟨98,679753031,679753482⟩,
⟨128,886948857,886949448⟩]
theorem checked14780 : checkPrefixCuts (2^48) 1941176321 9 Manual.Count131072.C014780.packed 128 cuts14780 = true := by
 decide +kernel
def pointBounds14780 : List (Nat × Nat × Nat) := [(1941215232,96075005788830,96075383693226),(1941276672,96075416420415,96075794325084)]
theorem point_links_checked14780 : (cuts14780.take 2).map (fun c => (1941176321-1+2*2^9*c.k,96074736667384+c.lower,96075114571602+c.upper)) = pointBounds14780 := by
 decide +kernel
def cuts14781 : List PrefixCut := [⟨30,209657409,209657548⟩,
⟨90,624322664,624323084⟩,
⟨128,880219605,880220197⟩]
theorem checked14781 : checkPrefixCuts (2^48) 1941307393 9 Manual.Count131072.C014781.packed 128 cuts14781 = true := by
 decide +kernel
def pointBounds14781 : List (Nat × Nat × Nat) := [(1941338112,96075833273650,96076211178598),(1941399552,96076247938905,96076625844134)]
theorem point_links_checked14781 : (cuts14781.take 2).map (fun c => (1941307393-1+2*2^9*c.k,96075623616241+c.lower,96076001521050+c.upper)) = pointBounds14781 := by
 decide +kernel
def cuts14782 : List PrefixCut := [⟨22,153535715,153535818⟩,
⟨82,561215739,561216114⟩,
⟨128,884944059,884944649⟩]
theorem checked14782 : checkPrefixCuts (2^48) 1941438465 9 Manual.Count131072.C014782.packed 128 cuts14782 = true := by
 decide +kernel
def pointBounds14782 : List (Nat × Nat × Nat) := [(1941460992,96076657371561,96077035277065),(1941522432,96077065051585,96077442957361)]
theorem point_links_checked14782 : (cuts14782.take 2).map (fun c => (1941438465-1+2*2^9*c.k,96076503835846+c.lower,96076881741247+c.upper)) = pointBounds14782 := by
 decide +kernel
def cuts14783 : List PrefixCut := [⟨14,96986485,96986550⟩,
⟨74,508989785,508990130⟩,
⟨128,885609204,885609800⟩]
theorem checked14783 : checkPrefixCuts (2^48) 1941569537 9 Manual.Count131072.C014783.packed 128 cuts14783 = true := by
 decide +kernel
def pointBounds14783 : List (Nat × Nat × Nat) := [(1941583872,96077485766390,96077863672446),(1941645312,96077897769690,96078275676026)]
theorem point_links_checked14783 : (cuts14783.take 2).map (fun c => (1941569537-1+2*2^9*c.k,96077388779905+c.lower,96077766685896+c.upper)) = pointBounds14783 := by
 decide +kernel
def cuts14784 : List PrefixCut := [⟨6,41604334,41604362⟩,
⟨66,457785267,457785575⟩,
⟨126,880766066,880766660⟩,
⟨128,894536635,894537238⟩]
theorem checked14784 : checkPrefixCuts (2^48) 1941700609 9 Manual.Count131072.C014784.packed 128 cuts14784 = true := by
 decide +kernel
def pointBounds14784 : List (Nat × Nat × Nat) := [(1941706752,96078315993443,96078693900058),(1941768192,96078732174376,96079110081271),(1941829632,96079155155175,96079533062356)]
theorem point_links_checked14784 : (cuts14784.take 3).map (fun c => (1941700609-1+2*2^9*c.k,96078274389109+c.lower,96078652295696+c.upper)) = pointBounds14784 := by
 decide +kernel
def cuts14785 : List PrefixCut := [⟨58,401514457,401514723⟩,
⟨118,813452635,813453173⟩,
⟨128,888388624,888389209⟩]
theorem checked14785 : checkPrefixCuts (2^48) 1941831681 9 Manual.Count131072.C014785.packed 128 cuts14785 = true := by
 decide +kernel
def pointBounds14785 : List (Nat × Nat × Nat) := [(1941891072,96079570440201,96079948347657),(1941952512,96079982378379,96080360286107)]
theorem point_links_checked14785 : (cuts14785.take 2).map (fun c => (1941831681-1+2*2^9*c.k,96079168925744+c.lower,96079546832934+c.upper)) = pointBounds14785 := by
 decide +kernel
def cuts14786 : List PrefixCut := [⟨50,345540783,345541021⟩,
⟨110,761076273,761076789⟩,
⟨128,888473625,888474228⟩]
theorem checked14786 : checkPrefixCuts (2^48) 1941962753 9 Manual.Count131072.C014786.packed 128 cuts14786 = true := by
 decide +kernel
def pointBounds14786 : List (Nat × Nat × Nat) := [(1942013952,96080402855151,96080780763164),(1942075392,96080818390641,96081196298932)]
theorem point_links_checked14786 : (cuts14786.take 2).map (fun c => (1941962753-1+2*2^9*c.k,96080057314368+c.lower,96080435222143+c.upper)) = pointBounds14786 := by
 decide +kernel
def cuts14787 : List PrefixCut := [⟨42,293632491,293632687⟩,
⟨102,716967885,716968364⟩,
⟨128,895225558,895226156⟩]
theorem checked14787 : checkPrefixCuts (2^48) 1942093825 9 Manual.Count131072.C014787.packed 128 cuts14787 = true := by
 decide +kernel
def pointBounds14787 : List (Nat × Nat × Nat) := [(1942136832,96081239420484,96081617329058),(1942198272,96081662755878,96082040664735)]
theorem point_links_checked14787 : (cuts14787.take 2).map (fun c => (1942093825-1+2*2^9*c.k,96080945787993+c.lower,96081323696371+c.upper)) = pointBounds14787 := by
 decide +kernel
def cuts14788 : List PrefixCut := [⟨34,234339913,234340071⟩,
⟨94,655039971,655040410⟩,
⟨128,890817407,890818003⟩]
theorem checked14788 : checkPrefixCuts (2^48) 1942224897 9 Manual.Count131072.C014788.packed 128 cuts14788 = true := by
 decide +kernel
def pointBounds14788 : List (Nat × Nat × Nat) := [(1942259712,96082075353464,96082453262598),(1942321152,96082496053522,96082873962937)]
theorem point_links_checked14788 : (cuts14788.take 2).map (fun c => (1942224897-1+2*2^9*c.k,96081841013551+c.lower,96082218922527+c.upper)) = pointBounds14788 := by
 decide +kernel
def cuts14789 : List PrefixCut := [⟨26,179257570,179257692⟩,
⟨86,592105957,592106359⟩,
⟨128,882207747,882208343⟩]
theorem checked14789 : checkPrefixCuts (2^48) 1942355969 9 Manual.Count131072.C014789.packed 128 cuts14789 = true := by
 decide +kernel
def pointBounds14789 : List (Nat × Nat × Nat) := [(1942382592,96082911088528,96083288998222),(1942444032,96083323936915,96083701846889)]
theorem point_links_checked14789 : (cuts14789.take 2).map (fun c => (1942355969-1+2*2^9*c.k,96082731830958+c.lower,96083109740530+c.upper)) = pointBounds14789 := by
 decide +kernel
def cuts14790 : List PrefixCut := [⟨18,122443612,122443696⟩,
⟨78,530484045,530484405⟩,
⟨128,878380579,878381175⟩]
theorem checked14790 : checkPrefixCuts (2^48) 1942487041 9 Manual.Count131072.C014790.packed 128 cuts14790 = true := by
 decide +kernel
def pointBounds14790 : List (Nat × Nat × Nat) := [(1942505472,96083736482317,96084114392569),(1942566912,96084144522750,96084522433278)]
theorem point_links_checked14790 : (cuts14790.take 2).map (fun c => (1942487041-1+2*2^9*c.k,96083614038705+c.lower,96083991948873+c.upper)) = pointBounds14790 := by
 decide +kernel
def cuts14791 : List PrefixCut := [⟨10,69114548,69114596⟩,
⟨70,475825150,475825473⟩,
⟨128,871221841,871222426⟩]
theorem checked14791 : checkPrefixCuts (2^48) 1942618113 9 Manual.Count131072.C014791.packed 128 cuts14791 = true := by
 decide +kernel
def pointBounds14791 : List (Nat × Nat × Nat) := [(1942628352,96084561533832,96084939444644),(1942689792,96084968244434,96085346155521)]
theorem point_links_checked14791 : (cuts14791.take 2).map (fun c => (1942618113-1+2*2^9*c.k,96084492419284+c.lower,96084870330048+c.upper)) = pointBounds14791 := by
 decide +kernel
def cuts14792 : List PrefixCut := [⟨2,13619167,13619176⟩,
⟨62,428562302,428562588⟩,
⟨122,847114200,847114763⟩,
⟨128,891011410,891012001⟩]
theorem checked14792 : checkPrefixCuts (2^48) 1942749185 9 Manual.Count131072.C014792.packed 128 cuts14792 = true := by
 decide +kernel
def pointBounds14792 : List (Nat × Nat × Nat) := [(1942751232,96085377260292,96085755171650),(1942812672,96085792203427,96086170115062),(1942874112,96086210755325,96086588667237)]
theorem point_links_checked14792 : (cuts14792.take 3).map (fun c => (1942749185-1+2*2^9*c.k,96085363641125+c.lower,96085741552474+c.upper)) = pointBounds14792 := by
 decide +kernel
def cuts14793 : List PrefixCut := [⟨54,372468530,372468780⟩,
⟨114,789110695,789111226⟩,
⟨128,890806501,890807098⟩]
theorem checked14793 : checkPrefixCuts (2^48) 1942880257 9 Manual.Count131072.C014793.packed 128 cuts14793 = true := by
 decide +kernel
def pointBounds14793 : List (Nat × Nat × Nat) := [(1942935552,96086627121065,96087005033255),(1942996992,96087043763230,96087421675701)]
theorem point_links_checked14793 : (cuts14793.take 2).map (fun c => (1942880257-1+2*2^9*c.k,96086254652535+c.lower,96086632564475+c.upper)) = pointBounds14793 := by
 decide +kernel
def cuts14794 : List PrefixCut := [⟨46,315802477,315802696⟩,
⟨106,739081929,739082422⟩,
⟨128,890167092,890167687⟩]
theorem checked14794 : checkPrefixCuts (2^48) 1943011329 9 Manual.Count131072.C014794.packed 128 cuts14794 = true := by
 decide +kernel
def pointBounds14794 : List (Nat × Nat × Nat) := [(1943058432,96087461261513,96087839174269),(1943119872,96087884540965,96088262453995)]
theorem point_links_checked14794 : (cuts14794.take 2).map (fun c => (1943011329-1+2*2^9*c.k,96087145459036+c.lower,96087523371573+c.upper)) = pointBounds14794 := by
 decide +kernel
def cuts14795 : List PrefixCut := [⟨38,265807182,265807358⟩,
⟨98,686162868,686163334⟩,
⟨128,899232663,899233268⟩]
theorem checked14795 : checkPrefixCuts (2^48) 1943142401 9 Manual.Count131072.C014795.packed 128 cuts14795 = true := by
 decide +kernel
def pointBounds14795 : List (Nat × Nat × Nat) := [(1943181312,96088301433310,96088679346618),(1943242752,96088721788996,96089099702594)]
theorem point_links_checked14795 : (cuts14795.take 2).map (fun c => (1943142401-1+2*2^9*c.k,96088035626128+c.lower,96088413539260+c.upper)) = pointBounds14795 := by
 decide +kernel
def cuts14796 : List PrefixCut := [⟨30,210459213,210459353⟩,
⟨90,622822023,622822435⟩,
⟨128,889902225,889902815⟩]
theorem checked14796 : checkPrefixCuts (2^48) 1943273473 9 Manual.Count131072.C014796.packed 128 cuts14796 = true := by
 decide +kernel
def pointBounds14796 : List (Nat × Nat × Nat) := [(1943304192,96089145318004,96089523231881),(1943365632,96089557680814,96089935594963)]
theorem point_links_checked14796 : (cuts14796.take 2).map (fun c => (1943273473-1+2*2^9*c.k,96088934858791+c.lower,96089312772528+c.upper)) = pointBounds14796 := by
 decide +kernel
def cuts14797 : List PrefixCut := [⟨22,150773353,150773457⟩,
⟨82,563834273,563834648⟩,
⟨128,892304089,892304685⟩]
theorem checked14797 : checkPrefixCuts (2^48) 1943404545 9 Manual.Count131072.C014797.packed 128 cuts14797 = true := by
 decide +kernel
def pointBounds14797 : List (Nat × Nat × Nat) := [(1943427072,96089975534369,96090353448800),(1943488512,96090388595289,96090766509991)]
theorem point_links_checked14797 : (cuts14797.take 2).map (fun c => (1943404545-1+2*2^9*c.k,96089824761016+c.lower,96090202675343+c.upper)) = pointBounds14797 := by
 decide +kernel
def cuts14798 : List PrefixCut := [⟨14,97902156,97902222⟩,
⟨74,518322882,518323233⟩,
⟨128,896443935,896444542⟩]
theorem checked14798 : checkPrefixCuts (2^48) 1943535617 9 Manual.Count131072.C014798.packed 128 cuts14798 = true := by
 decide +kernel
def pointBounds14798 : List (Nat × Nat × Nat) := [(1943549952,96090814967261,96091192882250),(1943611392,96091235387987,96091613303261)]
theorem point_links_checked14798 : (cuts14798.take 2).map (fun c => (1943535617-1+2*2^9*c.k,96090717065105+c.lower,96091094980028+c.upper)) = pointBounds14798 := by
 decide +kernel
def cuts14799 : List PrefixCut := [⟨6,43734496,43734526⟩,
⟨66,453557221,453557527⟩,
⟨126,863656596,863657178⟩,
⟨128,877558044,877558634⟩]
theorem checked14799 : checkPrefixCuts (2^48) 1943666689 9 Manual.Count131072.C014799.packed 128 cuts14799 = true := by
 decide +kernel
def pointBounds14799 : List (Nat × Nat × Nat) := [(1943672832,96091657243536,96092035159096),(1943734272,96092067066261,96092444982097),(1943795712,96092477165636,96092855081748)]
theorem point_links_checked14799 : (cuts14799.take 3).map (fun c => (1943666689-1+2*2^9*c.k,96091613509040+c.lower,96091991424570+c.upper)) = pointBounds14799 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000149
