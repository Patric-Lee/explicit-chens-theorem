import PlattAssemblyKernel
import PlattCertificates.Count131072.C020736
import PlattCertificates.Count131072.C020737
import PlattCertificates.Count131072.C020738
import PlattCertificates.Count131072.C020739
import PlattCertificates.Count131072.C020740
import PlattCertificates.Count131072.C020741
import PlattCertificates.Count131072.C020742
import PlattCertificates.Count131072.C020743
import PlattCertificates.Count131072.C020744
import PlattCertificates.Count131072.C020745
import PlattCertificates.Count131072.C020746
import PlattCertificates.Count131072.C020747
import PlattCertificates.Count131072.C020748
import PlattCertificates.Count131072.C020749
import PlattCertificates.Count131072.C020750
import PlattCertificates.Count131072.C020751
import PlattCertificates.Count131072.C020752
import PlattCertificates.Count131072.C020753
import PlattCertificates.Count131072.C020754
import PlattCertificates.Count131072.C020755
import PlattCertificates.Count131072.C020756
import PlattCertificates.Count131072.C020757
import PlattCertificates.Count131072.C020758
import PlattCertificates.Count131072.C020759
import PlattCertificates.Count131072.C020760
import PlattCertificates.Count131072.C020761
import PlattCertificates.Count131072.C020762
import PlattCertificates.Count131072.C020763
import PlattCertificates.Count131072.C020764
import PlattCertificates.Count131072.C020765
import PlattCertificates.Count131072.C020766
import PlattCertificates.Count131072.C020767
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20736 : List PrefixCut := [⟨25,119545345,119545413⟩,
⟨109,529155521,529155826⟩,
⟨128,625015487,625015847⟩]
theorem checked20736 : checkPrefixCuts (2^48) 2721841153 9 Manual.Count131072.C020736.packed 128 cuts20736 = true := by
 decide +kernel
def pointBounds20736 : List (Nat × Nat × Nat) := [(2721866752,100488902853834,100489283497141),(2721952768,100489312464010,100489693107554)]
theorem point_links_checked20736 : (cuts20736.take 2).map (fun c => (2721841153-1+2*2^9*c.k,100488783308489+c.lower,100489163951728+c.upper)) = pointBounds20736 := by
 decide +kernel
def cuts20737 : List PrefixCut := [⟨65,311152191,311152372⟩,
⟨128,625192205,625192564⟩]
theorem checked20737 : checkPrefixCuts (2^48) 2721972225 9 Manual.Count131072.C020737.packed 128 cuts20737 = true := by
 decide +kernel
def pointBounds20737 : List (Nat × Nat × Nat) := [(2722038784,100489719476167,100490100119947)]
theorem point_links_checked20737 : (cuts20737.take 1).map (fun c => (2721972225-1+2*2^9*c.k,100489408323976+c.lower,100489788967575+c.upper)) = pointBounds20737 := by
 decide +kernel
def cuts20738 : List PrefixCut := [⟨21,103403045,103403108⟩,
⟨105,513284651,513284953⟩,
⟨128,621336516,621336879⟩]
theorem checked20738 : checkPrefixCuts (2^48) 2722103297 9 Manual.Count131072.C020738.packed 128 cuts20738 = true := by
 decide +kernel
def pointBounds20738 : List (Nat × Nat × Nat) := [(2722124800,100490136919226,100490517563247),(2722210816,100490546800832,100490927445092)]
theorem point_links_checked20738 : (cuts20738.take 2).map (fun c => (2722103297-1+2*2^9*c.k,100490033516181+c.lower,100490414160139+c.upper)) = pointBounds20738 := by
 decide +kernel
def cuts20739 : List PrefixCut := [⟨61,302747284,302747456⟩,
⟨128,624098323,624098683⟩]
theorem checked20739 : checkPrefixCuts (2^48) 2722234369 9 Manual.Count131072.C020739.packed 128 cuts20739 = true := by
 decide +kernel
def pointBounds20739 : List (Nat × Nat × Nat) := [(2722296832,100490957599981,100491338244474)]
theorem point_links_checked20739 : (cuts20739.take 1).map (fun c => (2722234369-1+2*2^9*c.k,100490654852697+c.lower,100491035497018+c.upper)) = pointBounds20739 := by
 decide +kernel
def cuts20740 : List PrefixCut := [⟨17,83438295,83438345⟩,
⟨101,497416732,497417019⟩,
⟨128,632856383,632856747⟩]
theorem checked20740 : checkPrefixCuts (2^48) 2722365441 9 Manual.Count131072.C020740.packed 128 cuts20740 = true := by
 decide +kernel
def pointBounds20740 : List (Nat × Nat × Nat) := [(2722382848,100491362389315,100491743034046),(2722468864,100491776367752,100492157012720)]
theorem point_links_checked20740 : (cuts20740.take 2).map (fun c => (2722365441-1+2*2^9*c.k,100491278951020+c.lower,100491659595701+c.upper)) = pointBounds20740 := by
 decide +kernel
def cuts20741 : List PrefixCut := [⟨57,276768131,276768295⟩,
⟨128,621246730,621247098⟩]
theorem checked20741 : checkPrefixCuts (2^48) 2722496513 9 Manual.Count131072.C020741.packed 128 cuts20741 = true := by
 decide +kernel
def pointBounds20741 : List (Nat × Nat × Nat) := [(2722554880,100492188575534,100492569220743)]
theorem point_links_checked20741 : (cuts20741.take 1).map (fun c => (2722496513-1+2*2^9*c.k,100491911807403+c.lower,100492292452448+c.upper)) = pointBounds20741 := by
 decide +kernel
def cuts20742 : List PrefixCut := [⟨13,61099532,61099568⟩,
⟨97,472454168,472454448⟩,
⟨128,624111420,624111789⟩]
theorem checked20742 : checkPrefixCuts (2^48) 2722627585 9 Manual.Count131072.C020742.packed 128 cuts20742 = true := by
 decide +kernel
def pointBounds20742 : List (Nat × Nat × Nat) := [(2722640896,100492594153665,100492974799114),(2722726912,100493005508301,100493386153994)]
theorem point_links_checked20742 : (cuts20742.take 2).map (fun c => (2722627585-1+2*2^9*c.k,100492533054133+c.lower,100492913699546+c.upper)) = pointBounds20742 := by
 decide +kernel
def cuts20743 : List PrefixCut := [⟨53,250070317,250070466⟩,
⟨128,619015872,619016233⟩]
theorem checked20743 : checkPrefixCuts (2^48) 2722758657 9 Manual.Count131072.C020743.packed 128 cuts20743 = true := by
 decide +kernel
def pointBounds20743 : List (Nat × Nat × Nat) := [(2722812928,100493407235870,100493787881801)]
theorem point_links_checked20743 : (cuts20743.take 1).map (fun c => (2722758657-1+2*2^9*c.k,100493157165553+c.lower,100493537811335+c.upper)) = pointBounds20743 := by
 decide +kernel
def cuts20744 : List PrefixCut := [⟨9,40419007,40419032⟩,
⟨93,450907727,450907991⟩,
⟨128,619192945,619193310⟩]
theorem checked20744 : checkPrefixCuts (2^48) 2722889729 9 Manual.Count131072.C020744.packed 128 cuts20744 = true := by
 decide +kernel
def pointBounds20744 : List (Nat × Nat × Nat) := [(2722898944,100493816600432,100494197246600),(2722984960,100494227089152,100494607735559)]
theorem point_links_checked20744 : (cuts20744.take 2).map (fun c => (2722889729-1+2*2^9*c.k,100493776181425+c.lower,100494156827568+c.upper)) = pointBounds20744 := by
 decide +kernel
def cuts20745 : List PrefixCut := [⟨49,232990687,232990826⟩,
⟨128,615855260,615855625⟩]
theorem checked20745 : checkPrefixCuts (2^48) 2723020801 9 Manual.Count131072.C020745.packed 128 cuts20745 = true := by
 decide +kernel
def pointBounds20745 : List (Nat × Nat × Nat) := [(2723070976,100494628365057,100495009011704)]
theorem point_links_checked20745 : (cuts20745.take 1).map (fun c => (2723020801-1+2*2^9*c.k,100494395374370+c.lower,100494776020878+c.upper)) = pointBounds20745 := by
 decide +kernel
def cuts20746 : List PrefixCut := [⟨5,24497160,24497175⟩,
⟨89,432673039,432673292⟩,
⟨128,619960305,619960668⟩]
theorem checked20746 : checkPrefixCuts (2^48) 2723151873 9 Manual.Count131072.C020746.packed 128 cuts20746 = true := by
 decide +kernel
def pointBounds20746 : List (Nat × Nat × Nat) := [(2723156992,100495035726790,100495416373678),(2723243008,100495443902669,100495824549795)]
theorem point_links_checked20746 : (cuts20746.take 2).map (fun c => (2723151873-1+2*2^9*c.k,100495011229630+c.lower,100495391876503+c.upper)) = pointBounds20746 := by
 decide +kernel
def cuts20747 : List PrefixCut := [⟨45,225009929,225010057⟩,
⟨128,622824493,622824861⟩]
theorem checked20747 : checkPrefixCuts (2^48) 2723282945 9 Manual.Count131072.C020747.packed 128 cuts20747 = true := by
 decide +kernel
def pointBounds20747 : List (Nat × Nat × Nat) := [(2723329024,100495856199864,100496236847228)]
theorem point_links_checked20747 : (cuts20747.take 1).map (fun c => (2723282945-1+2*2^9*c.k,100495631189935+c.lower,100496011837171+c.upper)) = pointBounds20747 := by
 decide +kernel
def cuts20748 : List PrefixCut := [⟨1,4237501,4237503⟩,
⟨85,412684672,412684907⟩,
⟨128,623621118,623621472⟩]
theorem checked20748 : checkPrefixCuts (2^48) 2723414017 9 Manual.Count131072.C020748.packed 128 cuts20748 = true := by
 decide +kernel
def pointBounds20748 : List (Nat × Nat × Nat) := [(2723415040,100496258251929,100496638899535),(2723501056,100496666699100,100497047346939)]
theorem point_links_checked20748 : (cuts20748.take 2).map (fun c => (2723414017-1+2*2^9*c.k,100496254014428+c.lower,100496634662032+c.upper)) = pointBounds20748 := by
 decide +kernel
def cuts20749 : List PrefixCut := [⟨41,200908367,200908483⟩,
⟨125,610569871,610570225⟩,
⟨128,623384502,623384864⟩]
theorem checked20749 : checkPrefixCuts (2^48) 2723545089 9 Manual.Count131072.C020749.packed 128 cuts20749 = true := by
 decide +kernel
def pointBounds20749 : List (Nat × Nat × Nat) := [(2723587072,100497078543913,100497459191987),(2723673088,100497488205417,100497868853729)]
theorem point_links_checked20749 : (cuts20749.take 2).map (fun c => (2723545089-1+2*2^9*c.k,100496877635546+c.lower,100497258283504+c.upper)) = pointBounds20749 := by
 decide +kernel
def cuts20750 : List PrefixCut := [⟨81,395800506,395800739⟩,
⟨128,629554878,629555244⟩]
theorem checked20750 : checkPrefixCuts (2^48) 2723676161 9 Manual.Count131072.C020750.packed 128 cuts20750 = true := by
 decide +kernel
def pointBounds20750 : List (Nat × Nat × Nat) := [(2723759104,100497896820554,100498277469107)]
theorem point_links_checked20750 : (cuts20750.take 1).map (fun c => (2723676161-1+2*2^9*c.k,100497501020048+c.lower,100497881668368+c.upper)) = pointBounds20750 := by
 decide +kernel
def cuts20751 : List PrefixCut := [⟨37,176604735,176604839⟩,
⟨121,581370705,581371050⟩,
⟨128,615470906,615471271⟩]
theorem checked20751 : checkPrefixCuts (2^48) 2723807233 9 Manual.Count131072.C020751.packed 128 cuts20751 = true := by
 decide +kernel
def pointBounds20751 : List (Nat × Nat × Nat) := [(2723845120,100498307179661,100498687828451),(2723931136,100498711945631,100499092594662)]
theorem point_links_checked20751 : (cuts20751.take 2).map (fun c => (2723807233-1+2*2^9*c.k,100498130574926+c.lower,100498511223612+c.upper)) = pointBounds20751 := by
 decide +kernel
def cuts20752 : List PrefixCut := [⟨77,363316389,363316603⟩,
⟨128,611721261,611721623⟩]
theorem checked20752 : checkPrefixCuts (2^48) 2723938305 9 Manual.Count131072.C020752.packed 128 cuts20752 = true := by
 decide +kernel
def pointBounds20752 : List (Nat × Nat × Nat) := [(2724017152,100499109362221,100499490011486)]
theorem point_links_checked20752 : (cuts20752.take 1).map (fun c => (2723938305-1+2*2^9*c.k,100498746045832+c.lower,100499126694883+c.upper)) = pointBounds20752 := by
 decide +kernel
def cuts20753 : List PrefixCut := [⟨33,157678802,157678893⟩,
⟨117,566229448,566229781⟩,
⟨128,620681233,620681599⟩]
theorem checked20753 : checkPrefixCuts (2^48) 2724069377 9 Manual.Count131072.C020753.packed 128 cuts20753 = true := by
 decide +kernel
def pointBounds20753 : List (Nat × Nat × Nat) := [(2724103168,100499515445895,100499896095399),(2724189184,100499923996541,100500304646287)]
theorem point_links_checked20753 : (cuts20753.take 2).map (fun c => (2724069377-1+2*2^9*c.k,100499357767093+c.lower,100499738416506+c.upper)) = pointBounds20753 := by
 decide +kernel
def cuts20754 : List PrefixCut := [⟨73,353052812,353053023⟩,
⟨128,619721585,619721950⟩]
theorem checked20754 : checkPrefixCuts (2^48) 2724200449 9 Manual.Count131072.C020754.packed 128 cuts20754 = true := by
 decide +kernel
def pointBounds20754 : List (Nat × Nat × Nat) := [(2724275200,100500331501138,100500712151128)]
theorem point_links_checked20754 : (cuts20754.take 1).map (fun c => (2724200449-1+2*2^9*c.k,100499978448326+c.lower,100500359098105+c.upper)) = pointBounds20754 := by
 decide +kernel
def cuts20755 : List PrefixCut := [⟨29,139479744,139479827⟩,
⟨113,551917813,551918139⟩,
⟨128,626613988,626614357⟩]
theorem checked20755 : checkPrefixCuts (2^48) 2724331521 9 Manual.Count131072.C020755.packed 128 cuts20755 = true := by
 decide +kernel
def pointBounds20755 : List (Nat × Nat × Nat) := [(2724361216,100500737649655,100501118299882),(2724447232,100501150087724,100501530738194)]
theorem point_links_checked20755 : (cuts20755.take 2).map (fun c => (2724331521-1+2*2^9*c.k,100500598169911+c.lower,100500978820055+c.upper)) = pointBounds20755 := by
 decide +kernel
def cuts20756 : List PrefixCut := [⟨69,333802862,333803054⟩,
⟨128,625757196,625757559⟩]
theorem checked20756 : checkPrefixCuts (2^48) 2724462593 9 Manual.Count131072.C020756.packed 128 cuts20756 = true := by
 decide +kernel
def pointBounds20756 : List (Nat × Nat × Nat) := [(2724533248,100501558586761,100501939237466)]
theorem point_links_checked20756 : (cuts20756.take 1).map (fun c => (2724462593-1+2*2^9*c.k,100501224783899+c.lower,100501605434412+c.upper)) = pointBounds20756 := by
 decide +kernel
def cuts20757 : List PrefixCut := [⟨25,118908032,118908099⟩,
⟨109,531513500,531513810⟩,
⟨128,620251929,620252291⟩]
theorem checked20757 : checkPrefixCuts (2^48) 2724593665 9 Manual.Count131072.C020757.packed 128 cuts20757 = true := by
 decide +kernel
def pointBounds20757 : List (Nat × Nat × Nat) := [(2724619264,100501969449127,100502350100070),(2724705280,100502382054595,100502762705781)]
theorem point_links_checked20757 : (cuts20757.take 2).map (fun c => (2724593665-1+2*2^9*c.k,100501850541095+c.lower,100502231191971+c.upper)) = pointBounds20757 := by
 decide +kernel
def cuts20758 : List PrefixCut := [⟨65,314350158,314350342⟩,
⟨128,626936649,626937013⟩]
theorem checked20758 : checkPrefixCuts (2^48) 2724724737 9 Manual.Count131072.C020758.packed 128 cuts20758 = true := by
 decide +kernel
def pointBounds20758 : List (Nat × Nat × Nat) := [(2724791296,100502785143182,100503165794604)]
theorem point_links_checked20758 : (cuts20758.take 1).map (fun c => (2724724737-1+2*2^9*c.k,100502470793024+c.lower,100502851444262+c.upper)) = pointBounds20758 := by
 decide +kernel
def cuts20759 : List PrefixCut := [⟨21,103298602,103298661⟩,
⟨105,516794727,516795019⟩,
⟨128,632174664,632175023⟩]
theorem checked20759 : checkPrefixCuts (2^48) 2724855809 9 Manual.Count131072.C020759.packed 128 cuts20759 = true := by
 decide +kernel
def pointBounds20759 : List (Nat × Nat × Nat) := [(2724877312,100503201028275,100503581679936),(2724963328,100503614524400,100503995176294)]
theorem point_links_checked20759 : (cuts20759.take 2).map (fun c => (2724855809-1+2*2^9*c.k,100503097729673+c.lower,100503478381275+c.upper)) = pointBounds20759 := by
 decide +kernel
def cuts20760 : List PrefixCut := [⟨61,299859126,299859304⟩,
⟨128,624604034,624604399⟩]
theorem checked20760 : checkPrefixCuts (2^48) 2724986881 9 Manual.Count131072.C020760.packed 128 cuts20760 = true := by
 decide +kernel
def pointBounds20760 : List (Nat × Nat × Nat) := [(2725049344,100504029763463,100504410415602)]
theorem point_links_checked20760 : (cuts20760.take 1).map (fun c => (2724986881-1+2*2^9*c.k,100503729904337+c.lower,100504110556298+c.upper)) = pointBounds20760 := by
 decide +kernel
def cuts20761 : List PrefixCut := [⟨17,80875086,80875132⟩,
⟨101,493815559,493815850⟩,
⟨128,627156005,627156372⟩]
theorem checked20761 : checkPrefixCuts (2^48) 2725117953 9 Manual.Count131072.C020761.packed 128 cuts20761 = true := by
 decide +kernel
def pointBounds20761 : List (Nat × Nat × Nat) := [(2725135360,100504435383457,100504816035829),(2725221376,100504848323930,100505228976547)]
theorem point_links_checked20761 : (cuts20761.take 2).map (fun c => (2725117953-1+2*2^9*c.k,100504354508371+c.lower,100504735160697+c.upper)) = pointBounds20761 := by
 decide +kernel
def cuts20762 : List PrefixCut := [⟨57,278967351,278967511⟩,
⟨128,624337355,624337715⟩]
theorem checked20762 : checkPrefixCuts (2^48) 2725249025 9 Manual.Count131072.C020762.packed 128 cuts20762 = true := by
 decide +kernel
def pointBounds20762 : List (Nat × Nat × Nat) := [(2725307392,100505260631727,100505641284580)]
theorem point_links_checked20762 : (cuts20762.take 1).map (fun c => (2725249025-1+2*2^9*c.k,100504981664376+c.lower,100505362317069+c.upper)) = pointBounds20762 := by
 decide +kernel
def cuts20763 : List PrefixCut := [⟨13,61967334,61967368⟩,
⟨97,465057429,465057697⟩,
⟨128,616561513,616561869⟩]
theorem checked20763 : checkPrefixCuts (2^48) 2725380097 9 Manual.Count131072.C020763.packed 128 cuts20763 = true := by
 decide +kernel
def pointBounds20763 : List (Nat × Nat × Nat) := [(2725393408,100505667969065,100506048622152),(2725479424,100506071059160,100506451712481)]
theorem point_links_checked20763 : (cuts20763.take 2).map (fun c => (2725380097-1+2*2^9*c.k,100505606001731+c.lower,100505986654784+c.upper)) = pointBounds20763 := by
 decide +kernel
def cuts20764 : List PrefixCut := [⟨53,260351567,260351714⟩,
⟨128,619940019,619940378⟩]
theorem checked20764 : checkPrefixCuts (2^48) 2725511169 9 Manual.Count131072.C020764.packed 128 cuts20764 = true := by
 decide +kernel
def pointBounds20764 : List (Nat × Nat × Nat) := [(2725565440,100506482914811,100506863568367)]
theorem point_links_checked20764 : (cuts20764.take 1).map (fun c => (2725511169-1+2*2^9*c.k,100506222563244+c.lower,100506603216653+c.upper)) = pointBounds20764 := by
 decide +kernel
def cuts20765 : List PrefixCut := [⟨9,44922027,44922051⟩,
⟨93,449419743,449420005⟩,
⟨128,619600339,619600701⟩]
theorem checked20765 : checkPrefixCuts (2^48) 2725642241 9 Manual.Count131072.C020765.packed 128 cuts20765 = true := by
 decide +kernel
def pointBounds20765 : List (Nat × Nat × Nat) := [(2725651456,100506887425290,100507268079082),(2725737472,100507291923006,100507672577036)]
theorem point_links_checked20765 : (cuts20765.take 2).map (fun c => (2725642241-1+2*2^9*c.k,100506842503263+c.lower,100507223157031+c.upper)) = pointBounds20765 := by
 decide +kernel
def cuts20766 : List PrefixCut := [⟨49,241636069,241636212⟩,
⟨128,630412953,630413317⟩]
theorem checked20766 : checkPrefixCuts (2^48) 2725773313 9 Manual.Count131072.C020766.packed 128 cuts20766 = true := by
 decide +kernel
def pointBounds20766 : List (Nat × Nat × Nat) := [(2725823488,100507703739671,100508084393944)]
theorem point_links_checked20766 : (cuts20766.take 1).map (fun c => (2725773313-1+2*2^9*c.k,100507462103602+c.lower,100507842757732+c.upper)) = pointBounds20766 := by
 decide +kernel
def cuts20767 : List PrefixCut := [⟨5,23336573,23336588⟩,
⟨89,435953380,435953637⟩,
⟨128,627698039,627698403⟩]
theorem checked20767 : checkPrefixCuts (2^48) 2725904385 9 Manual.Count131072.C020767.packed 128 cuts20767 = true := by
 decide +kernel
def pointBounds20767 : List (Nat × Nat × Nat) := [(2725909504,100508115853128,100508496507637),(2725995520,100508528469935,100508909124686)]
theorem point_links_checked20767 : (cuts20767.take 2).map (fun c => (2725904385-1+2*2^9*c.k,100508092516555+c.lower,100508473171049+c.upper)) = pointBounds20767 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000023
