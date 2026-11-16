import PlattPointSubsetKernel
import PlattPointPackets.S1B000624
import PlattPointPackets.S1B000625
import PlattPointPackets.S1B000626
import PlattPointPackets.S1B000627
import PlattPointPackets.S1B000628
import PlattGlobalGrid.S6B000094
namespace ChenEffective.PlattWindow.PointCovers.S6B000094
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000624.points ++ ChenEffective.PlattWindow.PointPackets.S1B000625.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000626.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000627.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000628.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000094.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000094.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000094
