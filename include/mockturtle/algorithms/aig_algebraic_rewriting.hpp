/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting

  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"

namespace mockturtle
{

namespace detail
{

template<class Ntk>
class aig_algebraic_rewriting_impl
{
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl( Ntk& ntk )
    : ntk( ntk )
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
  }

  void run()
  {
    bool cont{true}; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) )
        {
          ntk.update_levels();
          cont = true;
        }
      });
    }
  }

private:
  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {
    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity( n ) )
      return true;
    /* TODO: add more rules here... */

    return false;
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity( node n )
  {
    std::vector<signal> signal_lv1, signal_lv2;
    signal sig_high1, sig_low1;
    signal sig_high2, sig_low2;
    int diff;

    // Level 1

    ntk.foreach_fanin(n, [&](signal sig){signal_lv1.push_back(sig);});
    if(signal_lv1.size() != 2)
      return false;

    diff = ntk.level(ntk.get_node(signal_lv1.at(0))) - ntk.level(ntk.get_node(signal_lv1.at(1)));

    if(diff >= 2){
      sig_high1 = signal_lv1.at(0);
      sig_low1 = signal_lv1.at(1);
    } else if(diff <= -2){
      sig_high1 = signal_lv1.at(1);
      sig_low1 = signal_lv1.at(0);
    } else {
      return false;
    }

    if(ntk.is_complemented(sig_high1) || ntk.fanout_size(ntk.get_node(sig_high1)) != 1)
      return false;

    // Level 2 (fanins of fanins)

    ntk.foreach_fanin(ntk.get_node(sig_high1), [&](signal sig){signal_lv2.push_back(sig);});
    if(signal_lv2.size() != 2)
      return false;

    if(ntk.level(ntk.get_node(signal_lv2.at(0))) >= ntk.level(ntk.get_node(signal_lv2.at(1)))){
      sig_high2 = signal_lv2.at(0);
      sig_low2 = signal_lv2.at(1);
    } else {
      sig_high2 = signal_lv2.at(1);
      sig_low2 = signal_lv2.at(0);
    }

    // OR gates
    if(ntk.is_complemented(sig_high2))
      sig_low1 = !sig_low1;
    if(ntk.is_complemented(sig_low1))
      sig_high2 = !sig_high2;

    ntk.replace_in_node(n, ntk.get_node(sig_low1), sig_high2);
    ntk.replace_in_node(ntk.get_node(sig_high1), ntk.get_node(sig_high2), sig_low1);

    return true;
  }

  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity( node n )
  {

    aig_network aig;

    std::vector<signal> sigLv1;
    std::vector<signal> sigLv2A;
    std::vector<signal> sigLv2B;

    node A;
    node B;

    ntk.foreach_fanin( n, [&]( signal sig )
                       { sigLv1.push_back( sig ); } ); //Extracts the fanin signals

    if ( sigLv1.size() != 2 )
      return false; //No optimization if we don't have 2 fanin signals

    A = ntk.get_node( sigLv1[0] );
    B = ntk.get_node( sigLv1[1] );

    ntk.foreach_fanin( A, [&]( signal sig )
                       { sigLv2A.push_back( sig ); } );
    ntk.foreach_fanin( B, [&]( signal sig )
                       { sigLv2B.push_back( sig ); } );

    if ( sigLv2A.size() != 2 || sigLv2B.size() != 2 || ntk.is_complemented( sigLv1[0] ) != ntk.is_complemented( sigLv1[1] ) )
      return false;
    if ( ntk.fanout_size( A ) != 1 || ntk.fanout_size( B ) != 1 )
      return false;

    signal comon;
    signal sigA;
    signal sigB;

    int i = 0;
    int j = 0;
    bool stop = false;
    bool find = false;

    while ( (!stop) && ( !find ) )
    {
      if ( sigLv2A[i] == sigLv2B[j])
      {
        find = true;
        comon = sigLv2A[i];
        if ( i == 0 )
          sigA = sigLv2A[1];
        else
          sigA = sigLv2A[0];

        if ( i == 0 )
          sigB = sigLv2B[1];
        else
          sigB = sigLv2B[0];
      }

      if ( i == 1 && j == 1 )
      {
        stop = true;
      }
      else if ( i == 1)
      {
        j = j + 1;
        i = 0;
      }
      else
      {
        i = i + 1;
      }
    }

    if ( !find )
      return false;

    signal tmp;
    inv_output( n );

    if ( ntk.is_complemented( sigLv1[0] ) )
      tmp = !comon;
    else
      tmp = comon;
    ntk.replace_in_node( n, A, tmp );

    if ( ntk.is_complemented( comon ))
      tmp = sigA;
    else
      tmp = !sigA;
    ntk.replace_in_node( B, ntk.get_node( comon ), tmp );

    if ( ntk.is_complemented( sigB ) )
      tmp = sigB;
    else
      tmp = !sigB;
    ntk.replace_in_node( B, ntk.get_node( sigB ), tmp );

    ntk.take_out_node( A );

    return true;

  }

  void inv_output(node const& n)
  {
    std::vector<signal> outS = foreach_fanout_sig_node( n );
    std::vector<node> nd = foreach_fanout_node( n );

    for ( int i = 0; i < outS.size(); i++ )
    {

      if ( ntk.is_complemented( outS[i] ) )
        ntk.replace_in_node( nd[i], n, outS[i] );
      else
        ntk.replace_in_node( nd[i], n, !outS[i] );

    }
    outS = foreach_fanout_PO( n );

    for ( int i = 0; i < outS.size(); i++ )
    {

      if ( ntk.is_complemented( outS[i] ) )
        ntk.replace_in_outputs( n, outS[i] );
      else
        ntk.replace_in_outputs( n, !outS[i] );

    }
  }

  std::vector<node> foreach_fanout_node(node const& n)
 {
   std::vector<node> nodOut;
   ntk.foreach_node( [&]( node nd )
       {
           ntk.foreach_fanin( nd, [&]( signal sig )
               {
                   if ( ntk.get_node( sig ) == n )
                       nodOut.push_back( nd );
               } );
       } );

   return nodOut;
 }

   std::string getType(node const&n)
   {
     if ( ntk.is_and( n ) )
       return "AND ";
     else if ( ntk.is_pi( n ) )
       return "PI ";
     else
       return "? ";

   }

   std::string getInv( signal const& sig)
   {
     if ( ntk.is_complemented( sig ) )
       return "! ";
     return "";
   }

 std::vector<signal> foreach_fanout_sig( node const& n )
 {
   std::vector<signal> sigOut;
   ntk.foreach_node( [&]( node nd )
   {
       ntk.foreach_fanin( nd, [&]( signal sig )
       {
                                            if ( ntk.get_node( sig ) == n )
                                              sigOut.push_back( sig );
       } );
   } );
   ntk.foreach_po( [&]( signal sig )
   {
                     if ( ntk.get_node( sig ) == n )
                       sigOut.push_back( sig );
   } );

   return sigOut;
 }

   std::vector<signal> foreach_fanout_sig_node( node const& n )
 {
   std::vector<signal> sigOut;
   ntk.foreach_node( [&]( node nd )
                     {
                       ntk.foreach_fanin( nd, [&]( signal sig )
                                          {
                                            if ( ntk.get_node( sig ) == n )
                                              sigOut.push_back( sig );
                                          } );
                     } );

   return sigOut;
 }

 std::vector<signal> foreach_fanout_PO(node const& n)
 {
   std::vector<signal> sigOut;
   ntk.foreach_po( [&]( signal sig )
                   {
                     if ( ntk.get_node( sig ) == n )
                       sigOut.push_back( sig );
                   } );

   return sigOut;
 }

private:
  Ntk& ntk;
};

} // namespace detail

/* Entry point for users to call */
template<class Ntk>
void aig_algebraic_rewriting( Ntk& ntk )
{
  static_assert( std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG" );

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */
