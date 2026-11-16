import PlattPointSubsetKernel
import PlattPointPackets.S2B000093
import PlattPointPackets.S2B000094
import PlattPointPackets.S2B000095
import PlattPointPackets.S2B000096
import PlattGlobalGrid.S7B000014
namespace ChenEffective.PlattWindow.PointCovers.S7B000014
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000093.points ++ ChenEffective.PlattWindow.PointPackets.S2B000094.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000095.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000096.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000014.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000014.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000014
