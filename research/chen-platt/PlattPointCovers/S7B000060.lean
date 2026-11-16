import PlattPointSubsetKernel
import PlattPointPackets.S2B000275
import PlattPointPackets.S2B000276
import PlattPointPackets.S2B000277
import PlattPointPackets.S2B000278
import PlattPointPackets.S2B000279
import PlattPointPackets.S2B000280
import PlattGlobalGrid.S7B000060
namespace ChenEffective.PlattWindow.PointCovers.S7B000060
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000275.points ++ ChenEffective.PlattWindow.PointPackets.S2B000276.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000277.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000278.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000279.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000280.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000060.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000060.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000060
